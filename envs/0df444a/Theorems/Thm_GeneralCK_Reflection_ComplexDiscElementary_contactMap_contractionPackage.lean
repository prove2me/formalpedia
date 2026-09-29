-- Prove2me | Theorems.Thm_GeneralCK_Reflection_ComplexDiscElementary_contactMap_contractionPackage
-- name    : GeneralCK.Reflection.ComplexDiscElementary.contactMap_contractionPackage
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-24T21:03:36.441816+00:00
-- url     : https://prove2.me/theorems/9cad9e99-2567-452e-8039-19e0aebc98c1
-- title:
--   A bounded complex entropy extension gives a contracting contact map
-- statement:
--   Let $D=\{c\in\mathbb C:|c|\le4/5\}$, let $E:\mathbb C\to\mathbb C$, and let $|\tau|\le7/10$. Assume $|E(c)|\le1103/1000$ for every $c\in D$ and $|E(c)-E(d)|\le(7/5)|c-d|$ for all $c,d\in D$. For $T(c)=\tau E(c)$, $$T(D)\subset D,\qquad |T(c)-T(d)|\le(49/50)|c-d|\quad(c,d\in D).$$ Thus the explicit analytic bounds supply a self-map with a contraction constant below one. This elementary interface is used before the later fixed-point existence argument.
-- source:
--   https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/ReflectionComplexDiscElementary.lean#L119-L134

import Mathlib.Analysis.Complex.Norm
import Mathlib.Topology.MetricSpace.Lipschitz
import Definitions.Def_GeneralCK_complex_contact

open GeneralCK.Reflection.ComplexDiscElementary
open Set

theorem GeneralCK.Reflection.ComplexDiscElementary.contactMap_contractionPackage
    {E : ℂ → ℂ} {τ : ℂ}
    (hτ : ‖τ‖ ≤ (7 / 10 : ℝ))
    (hBound : ∀ c ∈ Metric.closedBall (0 : ℂ) (4 / 5 : ℝ),
      ‖E c‖ ≤ (1103 / 1000 : ℝ))
    (hLip : LipschitzOnWith (7 / 5 : NNReal) E
      (Metric.closedBall 0 (4 / 5 : ℝ))) :
    MapsTo (contactMap E τ) (Metric.closedBall 0 (4 / 5 : ℝ))
        (Metric.closedBall 0 (4 / 5 : ℝ)) ∧
      LipschitzOnWith (49 / 50 : NNReal) (contactMap E τ)
        (Metric.closedBall 0 (4 / 5 : ℝ)) := by sorry
