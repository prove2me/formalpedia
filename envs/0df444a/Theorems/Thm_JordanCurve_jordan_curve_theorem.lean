-- Prove2me | Theorems.Thm_JordanCurve_jordan_curve_theorem
-- name    : JordanCurve.jordan_curve_theorem
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-09-25T00:06:57.726755+00:00
-- url     : https://prove2.me/theorems/d3ac13ce-f8b8-4f6b-8c02-fc6802c3a03a
-- title:
--   Jordan curve theorem
-- statement:
--   Let $\gamma:S^1\to\mathbb R^2$ be a continuous injective map, and let $J=\gamma(S^1)$ be its simple closed curve. Then the complement has exactly two connected components: a bounded interior $U$ and an unbounded exterior $V$. Both are open, they are disjoint, and their common boundary is precisely the curve: $$\mathbb R^2\setminus J=U\sqcup V,\qquad \partial U=\partial V=J.$$ In the formal statement, connectedness and the disjoint open partition ensure that these are the two connected components, rather than merely connected subsets.
-- source:
--   The classical Jordan curve theorem; compare A Proof of the Jordan Curve Theorem, https://doi.org/10.4236/ns.2019.1112037, statement of the Jordan Curve Theorem.

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.Bornology.Basic

namespace JordanCurve

theorem jordan_curve_theorem
    (γ : Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 →
      EuclideanSpace ℝ (Fin 2))
    (hγ : Continuous γ) (hinj : Function.Injective γ) :
    ∃ inside outside : Set (EuclideanSpace ℝ (Fin 2)),
      IsOpen inside ∧ IsOpen outside ∧
      IsConnected inside ∧ IsConnected outside ∧
      Bornology.IsBounded inside ∧ ¬ Bornology.IsBounded outside ∧
      Disjoint inside outside ∧
      inside ∪ outside = (Set.range γ)ᶜ ∧
      frontier inside = Set.range γ ∧
      frontier outside = Set.range γ := by sorry

end JordanCurve
