-- Prove2me | Theorems.Thm_IDivGeom_ExpFam_eq_3_19
-- name    : IDivGeom.ExpFam.eq_3_19
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T16:58:15.841872+00:00
-- url     : https://prove2.me/theorems/2c702153-821b-490d-9151-edfd3fa4573e
-- title:
--   (3.19) — at an inner point of A_R, F has a supporting hyperplane
-- statement:
--   With $f_1,\dots,f_k$, $R$, $A_R$ and $F$ as in (3.18), let $(a_1,\dots,a_k)$ be an inner point (a point of the topological interior in $E^k$) of $A_R$. Then there exists $(t_1,\dots,t_k)\in E^k$ such that
--   $$F(b_1,\dots,b_k)\ \ge\ F(a_1,\dots,a_k)+\sum_{i=1}^k t_i(b_i-a_i)\qquad\text{for all }(b_1,\dots,b_k)\in A_R.$$
--
--   The vector $(t_1,\dots,t_k)$ is the candidate parameter of the exponential-family density (3.2) of the I-projection in Theorem 3.3.
--
--   **Formalization Note** "Inner point" is the topological interior of $A_R$ in $E^k$ = `Fin k → ℝ`. $F$ is used through its real value, which is exact on $A_R$, where $F$ is finite by (3.18).
-- source:
--   Csiszár, I-divergence geometry of probability distributions and minimization problems, Ann. Probab. 3 (1975), p. 157 (PDF 12), (3.19), proof of Theorem 3.3

import Mathlib
import Definitions.Def_IDivGeom_ExpFam_Setting

open MeasureTheory InformationTheory Filter Topology
open scoped ENNReal NNReal

namespace IDivGeom.ExpFam

theorem eq_3_19 {X : Type*} [MeasurableSpace X]
    (k : ℕ) (f : Fin k → X → ℝ) (hf : ∀ i, Measurable (f i))
    (R : Measure X) [IsProbabilityMeasure R] :
    ∀ a ∈ interior (finiteSet f R), ∃ t : Fin k → ℝ, ∀ b ∈ finiteSet f R,
      (valueFn f R a).toReal + ∑ i, t i * (b i - a i) ≤ (valueFn f R b).toReal := by sorry

end IDivGeom.ExpFam
