-- Prove2me | Theorems.Thm_NoHair_kerrNewman_exterior_causalTransitivity
-- name    : NoHair.kerrNewman_exterior_causalTransitivity
-- status  : Open
-- author  : @Igor Valuev
-- created : 2026-11-22T20:53:58.176056+00:00
-- url     : https://prove2.me/theorems/fa4b8f00-b2ef-4577-97d8-59abfad7ce57
-- title:
--   Transitivity for regular future causal curves in the Kerr–Newman exterior
-- statement:
--   Two successive future causal segments in the exterior give a single future causal segment with the same outer endpoints. Here the relation uses globally $C^1$ representatives whose velocities are nonzero on the closed parameter interval. Proportional tangents at a joining point allow a regular reparametrization. A corner between distinct future rays can be rounded inside the timelike cone.
-- source:
--   E. Minguzzi, Lorentzian causality theory, Living Reviews in Relativity 22 (2019) 3, https://doi.org/10.1007/s41114-019-0019-x, sections on convex normal neighborhoods and the causal relation.

import Definitions.Def_NoHair_kerrNewman

open NoHair Set

theorem NoHair.kerrNewman_exterior_causalTransitivity (m a e : ℝ) (hp : IsKerrNewmanBlackHoleParams m a e)
    (T : VecField (kerrNewmanSpacetime a)) (hT : IsTimeOrientation (kerrNewmanMetricField m a e) T) :
    let U := kerrNewmanSpacetime a
    let D := (Subtype.val : U → E4) ⁻¹' kerrNewmanDOC m a e
    let g := kerrNewmanMetricField m a e
    ∀ p ∈ D, ∀ x ∈ D, ∀ q ∈ D,
      x ∈ causalFuture g T D p → q ∈ causalFuture g T D x → q ∈ causalFuture g T D p := by sorry
