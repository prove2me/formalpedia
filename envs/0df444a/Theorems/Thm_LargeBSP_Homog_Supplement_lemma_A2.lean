-- Prove2me | Theorems.Thm_LargeBSP_Homog_Supplement_lemma_A2
-- name    : LargeBSP.Homog.Supplement.lemma_A2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T16:57:41.180461+00:00
-- url     : https://prove2.me/theorems/613ee6ec-8566-45fc-a2dc-3903d7a56297
-- title:
--   Lemma A2, p. A10 (corrected: σ > 0) — the optimal discount is in ω₊(√N) ∩ o(N^β) for every β > 1/2
-- statement:
--   Let $X_1,X_2,\dots$ be i.i.d. nonnegative valuations with mean $\mu$, finite variance $\sigma^2>0$, and $\mathbb E[e^{tX_1}]<\infty$ for $|t|$ small (Assumption 5), and let the marginal cost be $0$. For each $N\ge1$ let $p^\star(N)\ge0$ maximize the pure-bundle revenue $p\,\mathbb P(V_N(N)\ge p)$, and let $g^\star(N)=N\mu-p^\star(N)$. Then
--   $$\frac{g^\star(N)}{\sqrt N}\longrightarrow+\infty\qquad\text{and}\qquad g^\star(N)=o(N^\beta)\quad\text{for every }\beta>\tfrac12.$$
--
--   The lemma places the optimal discount in the moderate-deviation range used in the proof of Theorem 6.
--
--   **Formalization Note** Both conclusions hold for every selection of optimal prices.
--
--   Differences from the source:
--
--   - reading: Lemma A2 states only c = 0 → the setting of §5.4 is assumed: i.i.d. nonnegative valuations with finite variance and Assumption 5; reason: the lemma is stated inside the proof of Theorem 6 and its proof uses the central limit and moderate deviation theorems of that setting
--   - correction: σ = 0 is not excluded → σ > 0; reason: the law X_n = 0 satisfies Assumption 5 with p⋆ = 0 and g⋆ = 0, refuting the growth and both normalized limits; only deterministic laws are excluded
--   - reading: p⋆(N) is an optimal solution of the pure-bundling problem, whose tie between buying and not buying is unspecified → the revenue is p·P(V_N(N) ≥ p) and p⋆(N) is any maximizer over p ≥ 0; reason: the strict event V_N(N) > p written in the proof has the same supremum but no maximizer for discrete laws, which would make the statement vacuous for them
-- source:
--   Abdallah, Asadpour & Reed, Large-Scale Bundle-Size Pricing: A Theoretical Analysis, author's manuscript (2021; Oper. Res. doi:10.1287/opre.2020.2097), SHA-256 1dfcad7675689de2118550b720b7488b45737ecd5ee5cd6085e5b5d0250d40cd, Lemma A2, p. A10; §5.4 and Assumption 5, p. 22

import Mathlib
import Definitions.Def_LargeBSP_Homog_Supplement_PureBundle

open MeasureTheory ProbabilityTheory Filter
open scoped Topology

namespace LargeBSP.Homog.Supplement

/-- Lemma A2 for every selection of optimal pure-bundle prices and every real beta>1/2.
The standard deviation is required positive; the zero law refutes the unqualified statement. -/
theorem lemma_A2 {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hXm : ∀ i, Measurable (X i)) (hXi : iIndepFun X P)
    (hXlaw : ∀ i, Measure.map (X i) P = ν)
    (hν0 : ν (Set.Iio 0) = 0) (hν1 : Integrable id ν) (hν2 : MemLp id 2 ν)
    (hσ : 0 < sd ν) (hcramer : CramerCondition ν)
    (pstar : ℕ → ℝ) (hp : ∀ N, 0 < N → IsPureOptimum P X N (pstar N)) :
    Tendsto (fun N : ℕ => discount ν pstar N / Real.sqrt N) atTop atTop ∧
    ∀ β : ℝ, 1 / 2 < β →
      Asymptotics.IsLittleO atTop (discount ν pstar) (fun N : ℕ => (N : ℝ) ^ β) := by sorry

end LargeBSP.Homog.Supplement
