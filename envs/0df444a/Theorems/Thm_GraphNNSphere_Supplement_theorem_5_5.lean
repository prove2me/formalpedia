-- Prove2me | Theorems.Thm_GraphNNSphere_Supplement_theorem_5_5
-- name    : GraphNNSphere.Supplement.theorem_5_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T09:57:59.907851+00:00
-- url     : https://prove2.me/theorems/f5ad5626-b865-4c55-b1f2-c25748072e58
-- title:
--   Theorem 5.5, pp.63–64 — local-exploration probability bound via the auxiliary exposure procedure
-- statement:
--   Let the data be uniform, with $\rho=\rho_\beta$, $0<\beta<\beta^*(c)$, in the logarithmic regime or $\rho=r_\gamma$, $0<\gamma<\gamma_c$, in the dense regime, and $\Delta=\lceil n^\beta\rceil$, resp. $\lceil e^{\gamma d}\rceil$. Fix $k\ge1$ and $\varepsilon>0$, and let $\iota_0>0$ be small enough depending on $\varepsilon$. Let $b_0=\theta_1+\iota_0$ in the logarithmic regime and $b_0=(1+\iota_0)\theta_1$ in the dense regime. Stop the auxiliary exposure procedure at the end of its first operation revealing a point of $C(q,b_0)$, or when the algorithm terminates earlier, keeping its exceptional stop when a nearest-neighbor list cannot be reconstructed; every triggering expansion completes its scan and exposure. Let $T_{\mathrm{near}}\le T$ count the expansions at distances in $(b_0,\theta_{\mathrm{trap}}+\rho_+]$ through this stop. There are $c'>0$, $n_0$ and, in the dense regime, $C=C(\gamma,\varepsilon)>0$ such that for all $n\ge n_0$, every fixed query $q$, the graphs $G_\rho$ and $N_\Delta$, and every local exploration algorithm with budget $(T,E)$ and $T\le n/(8\Delta)$,
--
--   $$\mathbb P\{\text{a point of }\mathrm{Top}_k(q)\text{ is evaluated}\}\le\mathbb E[T_{\mathrm{near}}]\,e^{-d(\eta_{\mathrm{gen}}-\varepsilon)}+E\,e_n+\mathbb P(C^c)+\exp(-e^{c'd}),$$
--
--   over the data and the algorithm's randomness, with $e_n=e^{-d(\eta_{\mathrm{entry}}-\varepsilon)}$ in the logarithmic regime and $e_n=e^{Cd}/n$ in the dense regime.
--
--   This bound converts the geometry of routes (the exponents $\eta_{\mathrm{gen}}$, $\eta_{\mathrm{entry}}$ of p.61) into an upper bound on the success of any adaptive local exploration, and yields the upper bounds of Theorems 5.3 and 5.9.
--
--   **Formalization Note** The graph is chosen by a flag ($N_\Delta$ or $G_\rho$), with $C$ the corresponding event. $\eta_{\mathrm{gen}}$ and $\eta_{\mathrm{entry}}$ are extended reals and $e^{-d(\eta-\varepsilon)}$ is the extended exponential. $\mathbb E[T_{\mathrm{near}}]$ is the integral over the product of the data law and the algorithm's randomness.
--
--   Differences from the source:
--   - encoding: O(·), o(1), Ω(d), e^{o(d)}, "with probability 1 − o(1)", "for all sufficiently large n" → explicit constants and vanishing sequences in the quantifier order of §2.1 (fixed parameters, constants, d(·), vanishing sequences, ∀ᶠ n), probabilities as measures of explicit measurable events; reason: Lean convention, as in the published goal Theorem 3.1
--   - generalization: local exploration algorithms whose entry labels follow a sequence fixed before sampling or are drawn afresh uniformly → algorithms whose j-th entry label is any function of the internal randomness (and whose operations are measurable); reason: conditioning on the randomness turns such an algorithm into one with a fixed sequence; the bound, uniform over algorithms, passes to the average, so the Lean statement specializes to the source
--   - encoding: every local exploration algorithm (probabilities over the data and its randomness) → algorithms with a probability space (Ω, μ) of internal randomness and measurable induced operations (IsMeasurableExplorer); reason: the probabilities in the statement are only defined for measurable algorithms; Theorem 5.9 names the requirement
--   - encoding: an algorithm with budget (T, E) → an arbitrary algorithm stopped at the first operation that would exceed T expansions or E entry requests; reason: an algorithm with that budget is unchanged by the truncation, and every truncated algorithm has the budget
--   - reading: P{a point of Top_k(q) is evaluated} → the probability that the budget-truncated algorithm evaluates a target in some operation; reason: the bound is the success bound (58) of the proof
--   - encoding: auxiliary exposure procedure and T_near → computed from the algorithm's actual history (revealed caps C(X_v, ρ₊), stops at the first reveal in C(q, b₀), the exceptional stop, or termination); reason: until its stop the procedure's lists are the true lists, so it follows the same history
--   - encoding: η_gen, η_entry (sup over chains in limiting coordinates) → extended-real suprema over ℓ ≥ 0 and chains, with φ₀ ∈ [θ_trap, π) (x₀ ∈ [L, ∞) in the dense regime); reason: p = −∞ when w ≥ 1; the endpoint φ₀ = π is a limit with p = −∞
--   - encoding: C = C(γ, ε), c′, n₀ → C chosen after (γ, ε) and before ι₀; c′ after ι₀; n₀ after d(·); reason: the paper's stated dependences
-- source:
--   Lu, Sharp Limits of Graph-Based Nearest Neighbor Search on the Sphere, STOC 2027 submission (manuscript sha256 93565bc5…), Theorem 5.5, pp.63–64 (PDF pp.65–66); auxiliary procedure, ρ₊ and C, p.63; η_gen, η_entry p.61

import Mathlib
import Definitions.Def_GraphNNSphere_rhoBeta
import Definitions.Def_GraphNNSphere_rGamma
import Definitions.Def_GraphNNSphere_dataLaw
import Definitions.Def_GraphNNSphere_thresholdGraph
import Definitions.Def_GraphNNSphere_nnGraph
import Definitions.Def_GraphNNSphere_betaStar
import Definitions.Def_GraphNNSphere_gammaC
import Definitions.Def_GraphNNSphere_logDim
import Definitions.Def_GraphNNSphere_IsDenseRegime
import Definitions.Def_GraphNNSphere_Supplement_LocalExplorer
import Definitions.Def_GraphNNSphere_Supplement_etaGen
import Definitions.Def_GraphNNSphere_Supplement_auxTnear

open MeasureTheory Filter Topology
open scoped ENNReal

namespace GraphNNSphere

namespace Supplement

/-- Theorem 5.5, local-exploration probability bound (Lu, *Sharp Limits of Graph-Based Nearest Neighbor Search on the Sphere*, STOC 2027 submission (manuscript sha256 93565bc5…), Theorem 5.5, pp.63–64). Uniform data,
`ρ = ρ_β` with `0 < β < β*(c)` (logarithmic regime) or `ρ = r_γ` with `0 < γ < γ_c` (dense regime), as in
§5.2. Fix `k ≥ 1`, `ε > 0` and `ι₀ > 0` small enough depending on `ε`; `b₀ = θ₁ + ι₀` (logarithmic) or
`(1 + ι₀)θ₁` (dense). Stop the auxiliary exposure procedure at the end of its first operation revealing
a point of `C(q, b₀)`, at its exceptional stop, or when the algorithm terminates; `T_near` counts the
expansions at query distances in `(b₀, θ_trap + ρ₊]` through this stop. There are `c' > 0`, `n₀` and, in
the dense regime, `C = C(γ, ε) > 0` such that for all `n ≥ n₀`, every fixed query `q`, both graphs `G_ρ` and
`N_Δ`, and every local exploration algorithm with budget `(T, E)`, `T ≤ n/(8Δ)`,
`P{a point of Top_k(q) is evaluated} ≤ E[T_near] e^{-d(η_gen-ε)} + E e_n + P(Cᶜ) + exp(-e^{c'd})`, with
`e_n = e^{-d(η_entry-ε)}` (logarithmic) or `e^{Cd}/n` (dense).

**Formalization Note** `ρ₊` solves `nF(ρ₊) = 2Δ`; `C` is `CEventNN` for `N_Δ` (`nn = true`) and the whole space
for `G_ρ`. `η_gen`, `η_entry` are the suprema over chains of p.61 in limiting coordinates, in `EReal`, and
`e^{-d(η-ε)}` is `EReal.exp`. The probability and `E[T_near]` are over the product of the data law and the
algorithm's randomness; the algorithm is measurable. In the dense regime `C` comes before `ι₀` (it is
`C(γ, ε)`) and `n₀` after `d(·)`. -/
theorem theorem_5_5 :
    (∀ k : ℕ, 1 ≤ k → ∀ c β ε : ℝ, 0 < c → 0 < β → β < betaStar c → 0 < ε →
      ∃ ιs : ℝ, 0 < ιs ∧ ∀ ι₀ : ℝ, 0 < ι₀ → ι₀ ≤ ιs →
      ∃ c' : ℝ, 0 < c' ∧ ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
        let d : ℕ := logDim c n
        let Δ : ℕ := ⌈(n : ℝ) ^ β⌉₊
        let ρ : ℝ := rhoBeta n d β
        let ρp : ℝ := rhoPlus n d Δ
        let b₀ : ℝ := theta1 n d + ι₀
        let b₁ : ℝ := thetaTrap n d ρ + ρp
        ∀ q : Sph d, ∀ nn : Bool, ∀ T E : ℕ, (T : ℝ) ≤ (n : ℝ) / (8 * (Δ : ℝ)) →
        ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
          (A : LocalExplorer n d Ω),
          IsMeasurableExplorer (fun X => if nn then nnGraph X Δ else thresholdGraph X ρ) q k A →
          ((dataLaw n d).prod μ)
              {p | explSucceeds (if nn then nnGraph p.1 Δ else thresholdGraph p.1 ρ) p.1 q k A p.2
                T E} ≤
            (∫⁻ p, auxTnear (if nn then nnGraph p.1 Δ else thresholdGraph p.1 ρ) p.1 q k A p.2 T E
                ρp b₀ b₁ nn Δ ∂((dataLaw n d).prod μ)) *
              EReal.exp (-(((d : ℝ) : EReal) * (etaGenLog c β - ((ε : ℝ) : EReal)))) +
            (E : ℝ≥0∞) * EReal.exp (-(((d : ℝ) : EReal) * (etaEntryLog c β - ((ε : ℝ) : EReal)))) +
            dataLaw n d (if nn then CEventNN ρp Δ else Set.univ)ᶜ +
            ENNReal.ofReal (Real.exp (-Real.exp (c' * (d : ℝ))))) ∧
    (∀ k : ℕ, 1 ≤ k → ∀ γ ε : ℝ, 0 < γ → γ < gammaC → 0 < ε →
      ∃ C : ℝ, 0 < C ∧ ∃ ιs : ℝ, 0 < ιs ∧ ∀ ι₀ : ℝ, 0 < ι₀ → ι₀ ≤ ιs →
      ∃ c' : ℝ, 0 < c' ∧ ∀ dd : ℕ → ℕ, IsDenseRegime dd → ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
        let d : ℕ := dd n
        let Δ : ℕ := ⌈Real.exp (γ * (d : ℝ))⌉₊
        let ρ : ℝ := rGamma n d γ
        let ρp : ℝ := rhoPlus n d Δ
        let b₀ : ℝ := (1 + ι₀) * theta1 n d
        let b₁ : ℝ := thetaTrap n d ρ + ρp
        ∀ q : Sph d, ∀ nn : Bool, ∀ T E : ℕ, (T : ℝ) ≤ (n : ℝ) / (8 * (Δ : ℝ)) →
        ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
          (A : LocalExplorer n d Ω),
          IsMeasurableExplorer (fun X => if nn then nnGraph X Δ else thresholdGraph X ρ) q k A →
          ((dataLaw n d).prod μ)
              {p | explSucceeds (if nn then nnGraph p.1 Δ else thresholdGraph p.1 ρ) p.1 q k A p.2
                T E} ≤
            (∫⁻ p, auxTnear (if nn then nnGraph p.1 Δ else thresholdGraph p.1 ρ) p.1 q k A p.2 T E
                ρp b₀ b₁ nn Δ ∂((dataLaw n d).prod μ)) *
              EReal.exp (-(((d : ℝ) : EReal) * (etaGenDense γ - ((ε : ℝ) : EReal)))) +
            (E : ℝ≥0∞) * ENNReal.ofReal (Real.exp (C * (d : ℝ)) / (n : ℝ)) +
            dataLaw n d (if nn then CEventNN ρp Δ else Set.univ)ᶜ +
            ENNReal.ofReal (Real.exp (-Real.exp (c' * (d : ℝ))))) := by sorry

end Supplement

end GraphNNSphere
