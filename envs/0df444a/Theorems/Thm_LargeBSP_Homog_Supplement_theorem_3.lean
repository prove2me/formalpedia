-- Prove2me | Theorems.Thm_LargeBSP_Homog_Supplement_theorem_3
-- name    : LargeBSP.Homog.Supplement.theorem_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T16:55:11.314047+00:00
-- url     : https://prove2.me/theorems/1e559bdd-5e23-4e92-b507-4b5d53e6f31d
-- title:
--   Theorem 3, p. 14 (corrected: continuity at c̄, positive surplus) — heterogeneous costs, i.i.d. valuations
-- statement:
--   Let $X_1,X_2,\dots$ be i.i.d. nonnegative valuations with distribution function $F_X$ and finite mean. Let the marginal costs $c_n\ge0$ be bounded, with empirical distribution functions converging to $F_C$ (Assumption 3), and let $\bar c=\int c\,dF_C(c)$. Write $\bar V_N(t)=V_N(\lfloor Nt\rfloor)/N$ and $\bar c_N(t)=c_N(\lfloor Nt\rfloor)/N$, the normalized value and cost of the customer's $\lfloor Nt\rfloor$ favourite items. Then:
--
--   1. for every $t\in[0,1]$, in probability,
--   $$\bar V_N(t)\Rightarrow\bar V(t)=\int_0^tF_X^{-1}(1-s)\,ds,\qquad \bar c_N(t)\Rightarrow t\bar c;$$
--   2. $t^\star=\sup\{s\in(0,1):F_X^{-1}(1-s)\ge\bar c\}$ maximizes $\bar V(t)-t\bar c$ on $[0,1]$;
--   3. if $F_X$ is continuous at $\bar c$, then $t^\star=1-F_X(\bar c)$;
--   4. if $\mathbb E[(X_1-\bar c)^+]>0$, the optimal expected bundle-size pricing profit satisfies
--   $$\lim_{N\to\infty}\frac{\mathbb E[\pi(p_N^\star)]}{N\,\mathbb E[(X_1-\bar c)^+]}=1.$$
--
--   When valuations do not depend on costs, optimal bundle-size pricing behaves to first order as if every item cost $\bar c$.
--
--   **Formalization Note** Valuation laws with atoms are allowed, and tied items are ranked by lowest index, as in the model. The optimal profit is a supremum over menus. Assumptions 1 and 2 follow from i.i.d. integrable valuations and are not assumed separately.
--
--   Differences from the source:
--
--   - encoding: items and order statistics are indexed from 1, ties between equally good sizes are unspecified, and ⇒ denotes a limit → items are indexed from 0, the customer takes the smallest of equally good sizes, and ⇒ is convergence in probability; reason: these are the conventions of the mission's model, and every limit here is a constant
--   - correction: t⋆ = 1 − F_X(c̄) "if c is a continuity point of F_X", where c is not defined in this theorem → F_X is continuous at c̄; reason: the threshold and the formula are both evaluated at c̄, so the printed c is a slip
--   - correction: the ratio (13) tends to 1 with no restriction on the surplus → the ratio claim assumes E[(X_1 − c̄)^+] > 0; reason: otherwise the denominator is 0 (for example all valuations and costs equal to 0), and only those cases are excluded, from the ratio claim alone
--   - generalization: p. 9 mentions a technical tail condition (6) made "to simplify our proofs" → (6) is not assumed; reason: it is not one of Assumptions 1–3 defining the regime and neither the statement nor the proof of Theorem 3 uses it; Theorem 2 of the mission is stated the same way; the paper imposes (6) once on p. 9 for all its proofs, so dropping it generalizes the theorem
--   - reading: t⋆ = sup over s ∈ [0,1] → the supremum is over (0,1), and t⋆ is asserted to maximize V̄(t) − t c̄; reason: the quantile is defined on (0,1) and the supremum is the same; maximization is what t⋆ denotes in Theorem 1
-- source:
--   Abdallah, Asadpour & Reed, Large-Scale Bundle-Size Pricing: A Theoretical Analysis, author's manuscript (2021; Oper. Res. doi:10.1287/opre.2020.2097), SHA-256 1dfcad7675689de2118550b720b7488b45737ecd5ee5cd6085e5b5d0250d40cd, Theorem 3, p. 14; proof p. A3

import Mathlib
import Definitions.Def_LargeBSP_Homog_Supplement_Costs

open MeasureTheory ProbabilityTheory Filter
open scoped Topology

namespace LargeBSP.Homog.Supplement

/-- Theorem 3, all curve and optimizer clauses; the ratio is interpreted only at positive
limiting surplus. The continuity point in the printed theorem is the mean cost, not a free c. -/
theorem theorem_3 {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    (ν κ : Measure ℝ) [IsProbabilityMeasure ν] [IsProbabilityMeasure κ]
    (c : ℕ → ℝ)
    (hXm : ∀ i, Measurable (X i)) (hXi : iIndepFun X P)
    (hXlaw : ∀ i, Measure.map (X i) P = ν)
    (hν0 : ν (Set.Iio 0) = 0) (hν1 : Integrable id ν)
    (hκ0 : κ (Set.Iio 0) = 0) (hκ1 : Integrable id κ) (hc : CostRegime c κ) :
    (∀ t ∈ Set.Icc (0 : ℝ) 1,
      TendstoInMeasure P (fun N ω => Vbar (fun i => X i ω) N t) atTop
        (fun _ => Vlim ν t) ∧
      TendstoInMeasure P (fun N ω => cbar c (fun i => X i ω) N t) atTop
        (fun _ => t * meanCost κ)) ∧
    MaxFraction (fun t => Vlim ν t - t * meanCost κ) (tstar ν (meanCost κ)) ∧
    (ContinuousAt (cdf ν) (meanCost κ) →
      tstar ν (meanCost κ) = 1 - cdf ν (meanCost κ)) ∧
    ((0 < ∫ x, max (x - meanCost κ) 0 ∂ν) →
      Tendsto (fun N : ℕ => optProfit P X c N /
        ((N : ℝ) * ∫ x, max (x - meanCost κ) 0 ∂ν)) atTop (𝓝 1)) := by sorry

end LargeBSP.Homog.Supplement
