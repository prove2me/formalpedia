-- Prove2me | Theorems.Thm_NoHair_kerrNewman_exterior_localCausalClosure
-- name    : NoHair.kerrNewman_exterior_localCausalClosure
-- status  : Proved
-- author  : @Igor Valuev
-- created : 2026-11-22T20:53:53.908051+00:00
-- url     : https://prove2.me/theorems/dc92604d-4d3c-4446-b44c-506448dc15ff
-- title:
--   Local closure of the causal endpoint relation in the Kerr–Newman exterior
-- statement:
--   Every exterior point has an open neighborhood $V$ in the exterior on which pairs of causal endpoints have the following local limit property. If two endpoints in $V$ are limits of pairs joined by causal curves confined to $V$, they are causally related in the exterior. In a convex normal neighborhood the inverse exponential map identifies the local future with the closed future tangent cone.
-- source:
--   E. Minguzzi, Lorentzian causality theory, Living Reviews in Relativity 22 (2019) 3, https://doi.org/10.1007/s41114-019-0019-x, sections on convex normal neighborhoods and the causal relation.

import Definitions.Def_NoHair_kerrNewman

open NoHair Set

theorem NoHair.kerrNewman_exterior_localCausalClosure (m a e : ℝ) (hp : IsKerrNewmanBlackHoleParams m a e)
    (T : VecField (kerrNewmanSpacetime a)) (hT : IsTimeOrientation (kerrNewmanMetricField m a e) T) :
    let U := kerrNewmanSpacetime a
    let D := (Subtype.val : U → E4) ⁻¹' kerrNewmanDOC m a e
    let g := kerrNewmanMetricField m a e
    ∀ x ∈ D, ∃ V : Set U, IsOpen V ∧ x ∈ V ∧ V ⊆ D ∧
      ∀ z : U × U, z.1 ∈ V → z.2 ∈ V →
        z ∈ closure {y : U × U | y.1 ∈ V ∧ y.2 ∈ V ∧ y.2 ∈ causalFuture g T V y.1} →
          z.2 ∈ causalFuture g T D z.1 := by sorry
