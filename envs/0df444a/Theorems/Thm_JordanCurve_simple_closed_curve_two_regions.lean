-- Prove2me | Theorems.Thm_JordanCurve_simple_closed_curve_two_regions
-- name    : JordanCurve.simple_closed_curve_two_regions
-- status  : Open
-- author  : @Mazecto
-- created : 2026-09-25T00:15:57.107736+00:00
-- url     : https://prove2.me/theorems/5d7581c0-2803-49f6-a2af-da917bafc813
-- title:
--   Jordan separation into two regions
-- statement:
--   A continuous injective image $J$ of the unit circle in the plane has a complement partitioned into two disjoint nonempty open connected regions: one bounded and the other unbounded. Thus $$\mathbb R^2\setminus J=U\sqcup V.$$ These are exactly the two connected components of the complement.
-- source:
--   Jordan curve theorem, separation assertion; see A Proof of the Jordan Curve Theorem, https://doi.org/10.4236/ns.2019.1112037.

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.Bornology.Basic

namespace JordanCurve
theorem simple_closed_curve_two_regions
    (γ : Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 →
      EuclideanSpace ℝ (Fin 2))
    (hγ : Continuous γ) (hinj : Function.Injective γ) :
    ∃ inside outside : Set (EuclideanSpace ℝ (Fin 2)),
      IsOpen inside ∧ IsOpen outside ∧
      IsConnected inside ∧ IsConnected outside ∧
      Bornology.IsBounded inside ∧ ¬ Bornology.IsBounded outside ∧
      Disjoint inside outside ∧
      inside ∪ outside = (Set.range γ)ᶜ := by sorry
end JordanCurve
