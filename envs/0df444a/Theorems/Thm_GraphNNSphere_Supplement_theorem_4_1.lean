-- Prove2me | Theorems.Thm_GraphNNSphere_Supplement_theorem_4_1
-- name    : GraphNNSphere.Supplement.theorem_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T09:51:12.815222+00:00
-- url     : https://prove2.me/theorems/0750c802-940e-4d13-8064-3e9a2adde88e
-- title:
--   Theorem 4.1, p.28 — the dense nonuniform critical curve $\kappa=h(\gamma)$
-- statement:
--   Let $d=d(n)$ be in the dense regime, fix $k\ge1$, $\gamma>\gamma_c=\tfrac12\log2$ and $\kappa\ge0$, and let $\Delta=\lceil e^{\gamma d}\rceil$. Write $\kappa_0=\tfrac12\log(3/2)$ and $h(\gamma)=\tfrac12\log((e^{2\gamma}+2)/4)$. The data are $n$ independent points with law $P=f\,d\sigma_{d-1}$.
--
--   1. **(Above the curve.)** If $0\le\kappa\le\kappa_0$ and $\kappa<h(\gamma)$, then for every sufficiently large fixed $K$ (depending on $\gamma,\kappa$), every $(\kappa,K)$-regular sequence of sampling densities and every absolutely continuous query law $Q$ fixed before the data, with probability $1-e^{-\Omega(d)}$ there is a Borel query set $Q_D$ with $Q(Q_D)\ge1-e^{-\Omega(d)}$ such that $N_\Delta$ succeeds from every entry for every $q\in Q_D$. Every such run uses at most $H=O(1+\rho_{\min}^{-1})=e^{o(d)}$ complete expansions and has evaluation cost at most $1+\Delta H=e^{(\gamma+o(1))d}$. The implicit constants depend only on $k,K,\gamma,\kappa$.
--   2. **(Below the curve.)** If $\gamma\le\log2$ and $\kappa>h(\gamma)$, there are a positive sampling density $f$ with $\operatorname{ess\,sup}\log f-\operatorname{ess\,inf}\log f=\kappa d$ exactly, which is $(\kappa,K)$-regular for every fixed $K>0$, and an absolutely continuous query law $Q_n$ with $\sup_{p}Q_n(C(p,\theta))\to0$ for every fixed $0<\theta<\pi/2$, both fixed before the data, such that with probability $1-e^{-\Omega(d)}$ every navigation graph of degree at most $\Delta$ has, for every query outside a graph-dependent set of $Q_n$-probability $e^{-\Omega(d)}$, at least $e^{\Omega(d)}$ failing entries.
--
--   This is the sharp worst-case degree curve $e^{2\gamma}=4e^{2\kappa}-2$ for densities whose local variation is at most $e^{\kappa d}$: $N_\Delta$ succeeds above it and every graph of smaller degree fails below it.
--
--   **Formalization Note** $H$ is $C_H(1+1/\rho_{\min})$ for a constant $C_H$. The large-$n$ threshold comes before $Q$. Per-$n$ properties of the densities and laws are required for all large $n$.
--
--   Differences from the source:
--   - encoding: O(·), o(1), Ω(d), e^{o(d)}, "with probability 1 − o(1)", "for all sufficiently large n" → explicit constants and vanishing sequences in the quantifier order of §2.1 (fixed parameters, constants, d(·), vanishing sequences, ∀ᶠ n), probabilities as measures of explicit measurable events; reason: Lean convention, as in the published goal Theorem 3.1
--   - generalization: (a): "for all sufficiently large n" after Q → one large-n threshold for all absolutely continuous Q; reason: part (a) is the case κ̄ = κ of Theorem 4.3, whose threshold is independent of Q (p.30); the Lean statement specializes to the source
--   - generalization: (a): hypotheses on the density sequence (density, (κ, K)-regularity) for every n → required only for all large n; reason: the conclusion is asymptotic; a sequence with the properties for every n has them eventually
--   - reading: (b): "a positive density … exactly κd … (κ, K)-regular … and a query distribution Q_n" → the per-n properties (density, positivity, exact oscillation, absolute continuity, probability) hold for all large n; reason: the statement is asymptotic, and for small n the dimension can be 0, where no density exists
--   - encoding: H = O(1 + ρ_min^{−1}) = e^{o(d)}, cost ≤ 1 + ΔH = e^{(γ+o(1))d} → H := C_H(1 + 1/ρ_min), expansions ≤ H ≤ e^{ε_n d}, evaluations ≤ 1 + ΔH ≤ e^{(γ+ε_n)d}; reason: explicit constant and vanishing sequence
--   - encoding: log(1/ρ_min) = o(d) (in regularity) → ρ_min ≥ e^{−ε_n d} with ε_n → 0; reason: equivalent since ρ_min ≤ π; avoids the junk value log(1/0) = 0
--   - encoding: ess sup log f − ess inf log f → extended-real essential oscillation with log 0 = −∞; reason: same quantity; ∞ when f vanishes on a set of positive measure
--   - encoding: measurable / Borel query sets → MeasurableSet on the sphere (the subtype of ℝ^d with its Borel σ-algebra); reason: same sets
--   - encoding: failing entry → W_G(q; x₀) = ⊤ in ℕ∞; reason: base mission convention
-- source:
--   Lu, Sharp Limits of Graph-Based Nearest Neighbor Search on the Sphere, STOC 2027 submission (manuscript sha256 93565bc5…), Theorem 4.1, p.28 (PDF p.30); (κ, K)-regularity §2.5, p.18; h(γ) Eq. (11), p.19

import Mathlib
import Definitions.Def_GraphNNSphere_IsNavGraph
import Definitions.Def_GraphNNSphere_maxDeg
import Definitions.Def_GraphNNSphere_greedyRun
import Definitions.Def_GraphNNSphere_W
import Definitions.Def_GraphNNSphere_nnGraph
import Definitions.Def_GraphNNSphere_gammaC
import Definitions.Def_GraphNNSphere_IsDenseRegime
import Definitions.Def_GraphNNSphere_Supplement_sampleLaw
import Definitions.Def_GraphNNSphere_Supplement_rhoF
import Definitions.Def_GraphNNSphere_Supplement_essOscLog
import Definitions.Def_GraphNNSphere_Supplement_hDense
import Definitions.Def_GraphNNSphere_Supplement_IsRegular

open MeasureTheory Filter Topology

namespace GraphNNSphere

namespace Supplement

open Classical in
/-- Theorem 4.1, the dense nonuniform critical curve (Lu, *Sharp Limits of Graph-Based Nearest Neighbor Search on the Sphere*, STOC 2027 submission (manuscript sha256 93565bc5…), Theorem 4.1, p.28). Dense regime,
`γ > γ_c`, `κ ≥ 0`, `Δ = ⌈e^{γd}⌉`.

(a) If `κ ≤ κ₀ = ½ log(3/2)` and `κ < h(γ)`, then for all large fixed `K` (depending on `γ, κ`), all
`(κ, K)`-regular sampling densities and all absolutely continuous query laws `Q`, with probability
`1 - e^{-Ω(d)}` there is a Borel query set of `Q`-probability `1 - e^{-Ω(d)}` on which `N_Δ` succeeds
from every entry, every run using at most `H = O(1 + ρ_min^{-1}) = e^{o(d)}` complete expansions and
evaluation cost at most `1 + ΔH = e^{(γ+o(1))d}`; the constants depend only on `k, K, γ, κ`.

(b) If `γ ≤ log 2` and `κ > h(γ)`, there are a positive density whose `ess sup log f - ess inf log f`
is exactly `κd`, `(κ, K)`-regular for every `K > 0`, and a globally spread absolutely continuous query
law `Q_n`, such that with probability `1 - e^{-Ω(d)}` every navigation graph of degree at most `Δ` has,
for every query outside a graph-dependent set of `Q_n`-probability `e^{-Ω(d)}`, at least `e^{Ω(d)}`
failing entries.

**Formalization Note** Quantifier order: fixed parameters, then `K₀` (depending on `γ, κ`), then
`K` and `k`, then the constants, then `d(·)`, then the density sequence, then the vanishing sequence
(the `e^{o(d)}` depends on the density through `ρ_min`), then large `n`, then `Q`. `H` is
`C_H(1 + 1/ρ_min)`. Per-`n` properties of the densities are required for all large `n` (for small `n`
the dimension may be `0`). A failing entry has `W = ⊤`. -/
theorem theorem_4_1 :
    (∀ γ κ : ℝ, gammaC < γ → 0 ≤ κ → κ ≤ kappa0 → κ < hDense γ →
      ∃ K₀ : ℝ, ∀ K : ℝ, K₀ ≤ K → ∀ k : ℕ, 1 ≤ k →
      ∃ c₁ c₂ CH : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ 0 < CH ∧
      ∀ d : ℕ → ℕ, IsDenseRegime d →
      ∀ f : ∀ n, Sph (d n) → ℝ, (∀ᶠ n in atTop, IsDensity (d n) (f n)) →
        IsRegular d f γ κ K →
      ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧
      ∀ᶠ n : ℕ in atTop,
        CH * (1 + 1 / rhoMin n (d n) (f n)) ≤ Real.exp (ε n * (d n : ℝ)) ∧
        1 + (⌈Real.exp (γ * (d n : ℝ))⌉₊ : ℝ) * (CH * (1 + 1 / rhoMin n (d n) (f n))) ≤
          Real.exp ((γ + ε n) * (d n : ℝ)) ∧
        ∀ Q : Measure (Sph (d n)), IsProbabilityMeasure Q → Q ≪ unif (d n) →
        ∃ E : Set (Fin n → Sph (d n)), MeasurableSet E ∧
          1 - Real.exp (-(c₁ * (d n : ℝ))) ≤ (dataLawF n (d n) (f n) E).toReal ∧
          ∀ X ∈ E, ∃ QD : Set (Sph (d n)), MeasurableSet QD ∧
            1 - Real.exp (-(c₂ * (d n : ℝ))) ≤ (Q QD).toReal ∧
            ∀ q ∈ QD, ∀ x₀ : Fin n, ∃ moves expansions evals : ℕ,
              greedyRun (nnGraph X ⌈Real.exp (γ * (d n : ℝ))⌉₊) X q k x₀ =
                .success moves expansions evals ∧
              (expansions : ℝ) ≤ CH * (1 + 1 / rhoMin n (d n) (f n)) ∧
              (evals : ℝ) ≤ 1 + (⌈Real.exp (γ * (d n : ℝ))⌉₊ : ℝ) *
                (CH * (1 + 1 / rhoMin n (d n) (f n)))) ∧
    (∀ k : ℕ, 1 ≤ k → ∀ γ κ : ℝ, gammaC < γ → γ ≤ Real.log 2 → hDense γ < κ →
      ∃ c₁ c₂ c₃ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ 0 < c₃ ∧
      ∀ d : ℕ → ℕ, IsDenseRegime d →
      ∃ f : ∀ n, Sph (d n) → ℝ, ∃ Q : ∀ n, Measure (Sph (d n)),
        (∀ᶠ n in atTop, IsDensity (d n) (f n) ∧ (∀ x, 0 < f n x) ∧
          essOscLog (d n) (f n) Set.univ = ((κ * (d n : ℝ) : ℝ) : EReal) ∧
          IsProbabilityMeasure (Q n) ∧ Q n ≪ unif (d n)) ∧
        (∀ K : ℝ, 0 < K → IsRegular d f γ κ K) ∧ IsGloballySpread d Q ∧
        ∀ᶠ n : ℕ in atTop,
          ∃ E : Set (Fin n → Sph (d n)), MeasurableSet E ∧
            1 - Real.exp (-(c₁ * (d n : ℝ))) ≤ (dataLawF n (d n) (f n) E).toReal ∧
            ∀ X ∈ E, ∀ G : NavGraph n, IsNavGraph G → maxDeg G ≤ ⌈Real.exp (γ * (d n : ℝ))⌉₊ →
              ∃ B : Set (Sph (d n)), MeasurableSet B ∧
                (Q n B).toReal ≤ Real.exp (-(c₂ * (d n : ℝ))) ∧
                ∀ q ∉ B, Real.exp (c₃ * (d n : ℝ)) ≤
                  ((Finset.univ.filter (fun x₀ : Fin n => W G X q k x₀ = ⊤)).card : ℝ)) := by sorry

end Supplement

end GraphNNSphere
