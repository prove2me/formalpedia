-- Prove2me | Theorems.Thm_GraphNNSphere_Supplement_theorem_5_9
-- name    : GraphNNSphere.Supplement.theorem_5_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T09:59:43.000699+00:00
-- url     : https://prove2.me/theorems/649e4dc2-fcc6-4671-9b00-4121a7661cf6
-- title:
--   Theorem 5.9, p.78 — distinct-evaluation lower bound $\mathbb P\{V\le e^{(\gamma+\eta-\varepsilon)d}\}\le e^{-c_\varepsilon d}$
-- statement:
--   Let the data be uniform in the dense regime, fix $k\ge1$, $\tfrac12\log(4/3)\le\gamma<\gamma_c$ and $\varepsilon>0$, and put $\Delta=\lceil e^{\gamma d}\rceil$ and $\eta=\eta^*(\gamma)$. On either $G_{r_\gamma}$ or $N_\Delta$, consider any measurable local exploration algorithm, without an imposed expansion or entry-request budget. For each fixed query $q$, let $V$ be the number of distinct query–data distance evaluations through the first completed expansion or entry request that evaluates a point of $\mathrm{Top}_k(q)$, and $V=\infty$ if no target is found. Then for all sufficiently large $n$,
--
--   $$\mathbb P\{V\le e^{(\gamma+\eta-\varepsilon)d}\}\le e^{-c_\varepsilon d},\qquad c_\varepsilon=\frac{\min\{\varepsilon,\eta/2\}}{16},$$
--
--   over the data and the algorithm's randomness. The constants and the threshold for $n$ are uniform in the query and the algorithm. Caches may be shared, and every expansion scans its complete list, including one that finds a target.
--
--   This is the lower-bound half of Theorem 5.1 in quantitative form, with an explicit exponential rate.
--
--   **Formalization Note** The threshold comes before the query, the graph and the algorithm. $V$ is the explorer's cost with no budget.
--
--   Differences from the source:
--   - encoding: O(·), o(1), Ω(d), e^{o(d)}, "with probability 1 − o(1)", "for all sufficiently large n" → explicit constants and vanishing sequences in the quantifier order of §2.1 (fixed parameters, constants, d(·), vanishing sequences, ∀ᶠ n), probabilities as measures of explicit measurable events; reason: Lean convention, as in the published goal Theorem 3.1
--   - generalization: local exploration algorithms whose entry labels follow a sequence fixed before sampling or are drawn afresh uniformly → algorithms whose j-th entry label is any function of the internal randomness (and whose operations are measurable); reason: conditioning on the randomness turns such an algorithm into one with a fixed sequence; the bound, uniform over algorithms, passes to the average, so the Lean statement specializes to the source
--   - encoding: measurable local exploration algorithm → a probability space (Ω, μ) of internal randomness and measurable induced operations (IsMeasurableExplorer); reason: measurability of the policy in its history implies measurability of the induced operations
--   - encoding: V ≤ e^{(γ+η−ε)d} with V = ∞ if no target is found → V is a finite m with m ≤ e^{(γ+η−ε)d}; reason: V = ∞ never satisfies the bound
-- source:
--   Lu, Sharp Limits of Graph-Based Nearest Neighbor Search on the Sphere, STOC 2027 submission (manuscript sha256 93565bc5…), Theorem 5.9, p.78 (PDF p.80); η*(γ) Eq. (50), p.54

import Mathlib
import Definitions.Def_GraphNNSphere_rGamma
import Definitions.Def_GraphNNSphere_dataLaw
import Definitions.Def_GraphNNSphere_thresholdGraph
import Definitions.Def_GraphNNSphere_nnGraph
import Definitions.Def_GraphNNSphere_IsDenseRegime
import Definitions.Def_GraphNNSphere_Supplement_etaStarDense
import Definitions.Def_GraphNNSphere_Supplement_LocalExplorer

open MeasureTheory Filter Topology

namespace GraphNNSphere

namespace Supplement

/-- Theorem 5.9, distinct-evaluation lower bound in the near-threshold band (Lu, *Sharp Limits of Graph-Based Nearest Neighbor Search on the Sphere*, STOC 2027 submission (manuscript sha256 93565bc5…), Theorem 5.9,
p.78). Uniform data, dense regime, `½ log(4/3) ≤ γ < γ_c`, `ε > 0`, `Δ = ⌈e^{γd}⌉`, `η = η*(γ)`. On
`G_{r_γ}` or `N_Δ`, for every measurable local exploration algorithm without a budget and every
fixed query, the number `V` of distinct query–data evaluations through the first operation that
evaluates a point of `Top_k(q)` (`V = ∞` if none) satisfies, for all large `n`,
`P{V ≤ e^{(γ+η-ε)d}} ≤ e^{-c_ε d}`, `c_ε = min{ε, η/2}/16`, over the data and the algorithm's randomness;
the threshold is uniform in the query and the algorithm.

**Formalization Note** The graph is `G_{r_γ}` (`nn = false`) or `N_Δ` (`nn = true`). The algorithm's
randomness is a probability space `(Ω, μ)` independent of the sample. `V` is `explCost` with budgets
`⊤`, so caches are shared and every expansion scans its full list. -/
theorem theorem_5_9 :
    ∀ k : ℕ, 1 ≤ k → ∀ γ ε : ℝ, InBandDense γ → 0 < ε →
      ∀ d : ℕ → ℕ, IsDenseRegime d → ∀ᶠ n : ℕ in atTop,
        ∀ q : Sph (d n), ∀ nn : Bool,
        ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
          (A : LocalExplorer n (d n) Ω),
          IsMeasurableExplorer (fun X => if nn then nnGraph X ⌈Real.exp (γ * (d n : ℝ))⌉₊
            else thresholdGraph X (rGamma n (d n) γ)) q k A →
          ((dataLaw n (d n)).prod μ)
            {p | ∃ m : ℕ, explCost (if nn then nnGraph p.1 ⌈Real.exp (γ * (d n : ℝ))⌉₊
                else thresholdGraph p.1 (rGamma n (d n) γ)) p.1 q k A p.2 ⊤ ⊤ = m ∧
              (m : ℝ) ≤ Real.exp ((γ + etaStarDense γ - ε) * (d n : ℝ))} ≤
            ENNReal.ofReal (Real.exp (-(min ε (etaStarDense γ / 2) / 16 * (d n : ℝ)))) := by sorry

end Supplement

end GraphNNSphere
