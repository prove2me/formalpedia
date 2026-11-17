-- Prove2me | Theorems.Thm_GraphNNSphere_Supplement_theorem_5_3
-- name    : GraphNNSphere.Supplement.theorem_5_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T09:56:38.242652+00:00
-- url     : https://prove2.me/theorems/6d9c2613-e0f0-4c35-a338-372520dfa7d2
-- title:
--   Theorem 5.3, p.60 — single-start success $p_1=e^{-d(\eta^*+o(1))}$ and local exploration
-- statement:
--   Let the data be uniform in either regime, with $\Delta$ in the near-threshold band: in the logarithmic regime $\Delta=\lceil n^\beta\rceil$, $\rho=\rho_\beta$, $0<\beta<\beta^*(c)$ and $\lim\theta_{\mathrm{trap}}\le\lim\rho$; in the dense regime $\Delta=\lceil e^{\gamma d}\rceil$, $\rho=r_\gamma$, $\tfrac12\log(4/3)\le\gamma<\gamma_c$. Fix $k\ge1$. For each fixed query and each of $G_\rho$ and $N_\Delta$, let $p_1$ be the probability, over the data and a uniform random entry, that one greedy run succeeds on the chosen graph. Then
--
--   $$p_1=e^{-d(\eta^*+o(1))},$$
--
--   with $\eta^*$ the exponent (55) (equal to (50) in the dense regime), and every local exploration algorithm on that graph with budget $(T,E)$, $T\le n/(8\Delta)$ and $E\ge1$, succeeds with probability at most $e^{o(d)}(T+E)p_1$ over the data and its internal randomness. The $o(d)$ term is independent of the algorithm and of $T,E$.
--
--   Intermediate local moves, caching and adaptive choices therefore do not improve on independent single starts by more than a subexponential factor per operation.
--
--   **Formalization Note** $p_1=e^{-d(\eta^*+o(1))}$ is the two-sided bound $e^{-d(\eta^*+\delta_n)}\le p_1\le e^{-d(\eta^*-\delta_n)}$, and the $o(d)$ is $\delta_n d$ with the same $\delta_n\to0$. The query is a sequence $q_n$ fixed before $\delta_n$; the graph is chosen before it as well.
--
--   Differences from the source:
--   - encoding: O(·), o(1), Ω(d), e^{o(d)}, "with probability 1 − o(1)", "for all sufficiently large n" → explicit constants and vanishing sequences in the quantifier order of §2.1 (fixed parameters, constants, d(·), vanishing sequences, ∀ᶠ n), probabilities as measures of explicit measurable events; reason: Lean convention, as in the published goal Theorem 3.1
--   - generalization: local exploration algorithms whose entry labels follow a sequence fixed before sampling or are drawn afresh uniformly → algorithms whose j-th entry label is any function of the internal randomness (and whose operations are measurable); reason: conditioning on the randomness turns such an algorithm into one with a fixed sequence; the bound, uniform over algorithms, passes to the average, so the Lean statement specializes to the source
--   - encoding: every local exploration algorithm (probabilities over the data and its randomness) → algorithms with a probability space (Ω, μ) of internal randomness and measurable induced operations (IsMeasurableExplorer); reason: the probabilities in the statement are only defined for measurable algorithms; Theorem 5.9 names the requirement
--   - encoding: an algorithm with budget (T, E) → an arbitrary algorithm stopped at the first operation that would exceed T expansions or E entry requests; reason: an algorithm with that budget is unchanged by the truncation, and every truncated algorithm has the budget
--   - encoding: uniform random entry label → uniformOn univ on Fin n, independent of the sample (product measure); reason: same law
--   - encoding: η* = −lim p(θ_trap, θ₁) (55) in the logarithmic regime → p evaluated at the limiting angles θ₁ → arcsin e^{−1/c}, ρ_β → arcsin e^{−(1−β)/c}; reason: p is continuous at the limit in the band (w < 1, Lemma 5.4(c)); the paper computes the limit this way (p.61)
--   - encoding: near-threshold band lim θ_trap ≤ R in the logarithmic regime → thetaTrapLim c β ≤ rhoLim c β with the limiting angles in closed form, together with 0 < β < β*(c); reason: same condition
--   - encoding: p₁ = e^{−d(η*+o(1))} → e^{−d(η*+δ_n)} ≤ p₁ ≤ e^{−d(η*−δ_n)}, δ_n → 0; reason: two-sided meaning of the equality
-- source:
--   Lu, Sharp Limits of Graph-Based Nearest Neighbor Search on the Sphere, STOC 2027 submission (manuscript sha256 93565bc5…), Theorem 5.3, p.60 (PDF p.62); band and η* (55), p.60

import Mathlib
import Definitions.Def_GraphNNSphere_rhoBeta
import Definitions.Def_GraphNNSphere_rGamma
import Definitions.Def_GraphNNSphere_dataLaw
import Definitions.Def_GraphNNSphere_W
import Definitions.Def_GraphNNSphere_thresholdGraph
import Definitions.Def_GraphNNSphere_nnGraph
import Definitions.Def_GraphNNSphere_logDim
import Definitions.Def_GraphNNSphere_IsDenseRegime
import Definitions.Def_GraphNNSphere_Supplement_etaStarDense
import Definitions.Def_GraphNNSphere_Supplement_etaStarLog
import Definitions.Def_GraphNNSphere_Supplement_LocalExplorer

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal

namespace GraphNNSphere

namespace Supplement

/-- Theorem 5.3, single-start success and local exploration (Lu, *Sharp Limits of Graph-Based Nearest Neighbor Search on the Sphere*, STOC 2027 submission (manuscript sha256 93565bc5…), Theorem 5.3, p.60). Uniform
data, either regime, `Δ` in the near-threshold band (`ρ = ρ_β`, `0 < β < β*(c)`, in the logarithmic
regime; `ρ = r_γ` in the dense regime), `k ≥ 1`. For each fixed query and each of `G_ρ` and `N_Δ`, the
probability `p₁` over the data and a uniform random entry that one greedy run succeeds satisfies
`p₁ = e^{-d(η*+o(1))}`, and every local exploration algorithm with budget `(T, E)`, `T ≤ n/(8Δ)`,
`E ≥ 1`, succeeds with probability at most `e^{o(d)}(T + E)p₁`, the `o(d)` independent of the algorithm
and of `T, E`.

**Formalization Note** `η*` is (55), `etaStarLog`, in the logarithmic regime and (50), `etaStarDense`,
in the dense regime, as the paper states. The query is a sequence `q_n` fixed before the `o(1)`
terms, and the graph is chosen by `nn` before them. `p₁ = e^{-d(η*+o(1))}` is the two-sided bound
`e^{-d(η*+δ_n)} ≤ p₁ ≤ e^{-d(η*-δ_n)}`, and the `o(d)` is `δ_n d` with the same `δ_n → 0`. Algorithms
are measurable (`IsMeasurableExplorer`). -/
theorem theorem_5_3 :
    (∀ k : ℕ, 1 ≤ k → ∀ c β : ℝ, 0 < c → InBandLog c β →
      ∀ q : ∀ n, Sph (logDim c n), ∀ nn : Bool,
      ∃ δ : ℕ → ℝ, Tendsto δ atTop (𝓝 0) ∧ ∀ᶠ n : ℕ in atTop,
        ENNReal.ofReal (Real.exp (-((logDim c n : ℝ) * (etaStarLog c β + δ n)))) ≤
          ((dataLaw n (logDim c n)).prod (uniformOn (Set.univ : Set (Fin n))))
            {p | W (if nn then nnGraph p.1 ⌈(n : ℝ) ^ β⌉₊
              else thresholdGraph p.1 (rhoBeta n (logDim c n) β)) p.1 (q n) k p.2 < ⊤} ∧
        ((dataLaw n (logDim c n)).prod (uniformOn (Set.univ : Set (Fin n))))
            {p | W (if nn then nnGraph p.1 ⌈(n : ℝ) ^ β⌉₊
              else thresholdGraph p.1 (rhoBeta n (logDim c n) β)) p.1 (q n) k p.2 < ⊤} ≤
          ENNReal.ofReal (Real.exp (-((logDim c n : ℝ) * (etaStarLog c β - δ n)))) ∧
        ∀ T E : ℕ, (T : ℝ) ≤ (n : ℝ) / (8 * (⌈(n : ℝ) ^ β⌉₊ : ℝ)) → 1 ≤ E →
        ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
          (A : LocalExplorer n (logDim c n) Ω),
          IsMeasurableExplorer (fun X => if nn then nnGraph X ⌈(n : ℝ) ^ β⌉₊
            else thresholdGraph X (rhoBeta n (logDim c n) β)) (q n) k A →
          ((dataLaw n (logDim c n)).prod μ)
              {p | explSucceeds (if nn then nnGraph p.1 ⌈(n : ℝ) ^ β⌉₊
                else thresholdGraph p.1 (rhoBeta n (logDim c n) β)) p.1 (q n) k A p.2 T E} ≤
            ENNReal.ofReal (Real.exp (δ n * (logDim c n : ℝ))) * ((T + E : ℝ≥0∞) *
              ((dataLaw n (logDim c n)).prod (uniformOn (Set.univ : Set (Fin n))))
                {p | W (if nn then nnGraph p.1 ⌈(n : ℝ) ^ β⌉₊
                  else thresholdGraph p.1 (rhoBeta n (logDim c n) β)) p.1 (q n) k p.2 < ⊤})) ∧
    (∀ k : ℕ, 1 ≤ k → ∀ γ : ℝ, InBandDense γ → ∀ d : ℕ → ℕ, IsDenseRegime d →
      ∀ q : ∀ n, Sph (d n), ∀ nn : Bool,
      ∃ δ : ℕ → ℝ, Tendsto δ atTop (𝓝 0) ∧ ∀ᶠ n : ℕ in atTop,
        ENNReal.ofReal (Real.exp (-((d n : ℝ) * (etaStarDense γ + δ n)))) ≤
          ((dataLaw n (d n)).prod (uniformOn (Set.univ : Set (Fin n))))
            {p | W (if nn then nnGraph p.1 ⌈Real.exp (γ * (d n : ℝ))⌉₊
              else thresholdGraph p.1 (rGamma n (d n) γ)) p.1 (q n) k p.2 < ⊤} ∧
        ((dataLaw n (d n)).prod (uniformOn (Set.univ : Set (Fin n))))
            {p | W (if nn then nnGraph p.1 ⌈Real.exp (γ * (d n : ℝ))⌉₊
              else thresholdGraph p.1 (rGamma n (d n) γ)) p.1 (q n) k p.2 < ⊤} ≤
          ENNReal.ofReal (Real.exp (-((d n : ℝ) * (etaStarDense γ - δ n)))) ∧
        ∀ T E : ℕ, (T : ℝ) ≤ (n : ℝ) / (8 * (⌈Real.exp (γ * (d n : ℝ))⌉₊ : ℝ)) → 1 ≤ E →
        ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
          (A : LocalExplorer n (d n) Ω),
          IsMeasurableExplorer (fun X => if nn then nnGraph X ⌈Real.exp (γ * (d n : ℝ))⌉₊
            else thresholdGraph X (rGamma n (d n) γ)) (q n) k A →
          ((dataLaw n (d n)).prod μ)
              {p | explSucceeds (if nn then nnGraph p.1 ⌈Real.exp (γ * (d n : ℝ))⌉₊
                else thresholdGraph p.1 (rGamma n (d n) γ)) p.1 (q n) k A p.2 T E} ≤
            ENNReal.ofReal (Real.exp (δ n * (d n : ℝ))) * ((T + E : ℝ≥0∞) *
              ((dataLaw n (d n)).prod (uniformOn (Set.univ : Set (Fin n))))
                {p | W (if nn then nnGraph p.1 ⌈Real.exp (γ * (d n : ℝ))⌉₊
                  else thresholdGraph p.1 (rGamma n (d n) γ)) p.1 (q n) k p.2 < ⊤})) := by sorry

end Supplement

end GraphNNSphere
