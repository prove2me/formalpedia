-- Prove2me | Theorems.Thm_JordanCurve_jordan_complement_two_distinct_regions
-- name    : JordanCurve.jordan_complement_two_distinct_regions
-- status  : Open
-- author  : @Mazecto
-- created : 2026-09-25T00:36:38.019615+00:00
-- url     : https://prove2.me/theorems/9aeb3c4c-2d87-444f-8c88-7c4d496fccdd
-- title:
--   Two distinct Jordan complementary regions
-- statement:
--   Every embedded circle in the plane has at least two disjoint complementary connected components, one bounded and one unbounded.
-- source:
--   https://github.com/leanprover-community/mathlib4/tree/master/Mathlib/Topology

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.Bornology.Basic

namespace JordanCurve

/-- Jordan disconnection: the complement has distinct components, one bounded
and one unbounded. The assertion that these are all the components is separate. -/
theorem jordan_complement_two_distinct_regions
    (γ : Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 →
      EuclideanSpace ℝ (Fin 2))
    (hγ : Continuous γ) (hinj : Function.Injective γ) :
    ∃ a b : EuclideanSpace ℝ (Fin 2),
      a ∉ Set.range γ ∧ b ∉ Set.range γ ∧
      Disjoint
        (connectedComponentIn ((Set.range γ)ᶜ) a)
        (connectedComponentIn ((Set.range γ)ᶜ) b) ∧
      Bornology.IsBounded (connectedComponentIn ((Set.range γ)ᶜ) a) ∧
      ¬ Bornology.IsBounded (connectedComponentIn ((Set.range γ)ᶜ) b) := by sorry

end JordanCurve
