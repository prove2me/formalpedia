-- Prove2me | Theorems.Thm_LargeBSP_Homog_Supplement_theorem_6
-- name    : LargeBSP.Homog.Supplement.theorem_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T16:58:11.900623+00:00
-- url     : https://prove2.me/theorems/59ff496c-2fcb-4fb5-b862-cc7d4817b19f
-- title:
--   Theorem 6, p. 22 (corrected: σ > 0) — discount and PPD gap of pure bundling are both ~ σ√(N log N)
-- statement:
--   Let $X_1,X_2,\dots$ be i.i.d. nonnegative valuations with mean $\mu$, variance $\sigma^2>0$, and $\mathbb E[e^{tX_1}]<\infty$ for $|t|$ small (Assumption 5), and let the marginal cost be $0$. For each $N\ge1$ let $p^\star(N)\ge0$ maximize the pure-bundle revenue $R_N(p)=p\,\mathbb P(V_N(N)\ge p)$, let $g^\star(N)=N\mu-p^\star(N)$, and let $\mathrm{PPD}=\sum_{n\le N}\mathbb E[X_n]$. Then
--   $$\frac{g^\star(N)}{\sigma\sqrt{N\log N}}\longrightarrow1\qquad(26)$$
--   and
--   $$\frac{\mathrm{PPD}-R_N(p^\star(N))}{\sigma\sqrt{N\log N}}\longrightarrow1.\qquad(27)$$
--
--   The optimal bundle price is $N\mu-\sigma\sqrt{N\log N}$ up to lower order, and this is also the second-order loss against perfect price discrimination.
--
--   **Formalization Note** The profit in (27) is the optimal pure-bundle profit, as defined before Assumption 5, and not the optimum over all bundle-size menus. Both limits hold for every selection of optimal prices.
--
--   Differences from the source:
--
--   - correction: σ = 0 is not excluded → σ > 0; reason: the law X_n = 0 satisfies Assumption 5 with p⋆ = 0 and g⋆ = 0, refuting the growth and both normalized limits; only deterministic laws are excluded
--   - reading: p⋆(N) is an optimal solution of the pure-bundling problem, whose tie between buying and not buying is unspecified → the revenue is p·P(V_N(N) ≥ p) and p⋆(N) is any maximizer over p ≥ 0; reason: the strict event V_N(N) > p written in the proof has the same supremum but no maximizer for discrete laws, which would make the statement vacuous for them
-- source:
--   Abdallah, Asadpour & Reed, Large-Scale Bundle-Size Pricing: A Theoretical Analysis, author's manuscript (2021; Oper. Res. doi:10.1287/opre.2020.2097), SHA-256 1dfcad7675689de2118550b720b7488b45737ecd5ee5cd6085e5b5d0250d40cd, Theorem 6, (26)–(27), p. 22; proof pp. A10–A13

import Mathlib
import Definitions.Def_LargeBSP_Homog_Supplement_PureBundle

open MeasureTheory ProbabilityTheory Filter
open scoped Topology

namespace LargeBSP.Homog.Supplement

/-- Both sharp limits of Theorem 6, with the same pure-bundle optimum and actual sd.
The correction excludes only the sigma=0 degeneracy of the normalized claims. -/
theorem theorem_6 {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hXm : ∀ i, Measurable (X i)) (hXi : iIndepFun X P)
    (hXlaw : ∀ i, Measure.map (X i) P = ν)
    (hν0 : ν (Set.Iio 0) = 0) (hν1 : Integrable id ν) (hν2 : MemLp id 2 ν)
    (hσ : 0 < sd ν) (hcramer : CramerCondition ν)
    (pstar : ℕ → ℝ) (hp : ∀ N, 0 < N → IsPureOptimum P X N (pstar N)) :
    Tendsto (fun N : ℕ => discount ν pstar N /
      (sd ν * Real.sqrt ((N : ℝ) * Real.log N))) atTop (𝓝 1) ∧
    Tendsto (fun N : ℕ =>
      (PPD P X (fun _ => 0) N - pureRevenue P X N (pstar N)) /
      (sd ν * Real.sqrt ((N : ℝ) * Real.log N))) atTop (𝓝 1) := by sorry

end LargeBSP.Homog.Supplement
