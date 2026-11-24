-- Prove2me | Theorems.Thm_GlobalTheory_CubeFace_diag_prod
-- name    : GlobalTheory.CubeFace.diag_prod
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T12:28:22.07981+00:00
-- url     : https://prove2.me/theorems/a65990f2-d04e-4407-b54d-d23c8991779a
-- title:
--   Cube Face: diag prod
-- statement:
--   The Cube Face construction uses the diag prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/CubeSectionFacesAndDoubling.lean#L143-L153
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/CubeSectionFacesAndDoubling.lean#L143-L153

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EntireApplyEqOfPeriodicOfSpanReal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_CubeSectionFacesAndDoubling
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Matrix Filter Topology
open scoped BigOperators Real
open GlobalTheory
open GlobalTheory.CubeFace

theorem GlobalTheory.CubeFace.diag_prod {V ι : Type*} [AddCommGroup V] [Module ℂ V] (c : ι → ι → V → ℂ)
    (a b d a' b' d' o : ι) (ho : c o o 0 = 1) (z : V) :
    ∏ J : Finset (Fin 3), c (diagChart a b d o J) (diagChart a' b' d' o J)
      (∑ i ∈ J, (![z, z, -z] : Fin 3 → V) i) ^ ((-1 : ℤ) ^ (3 - J.card)) =
      c a a' z ^ 3 * c b b' (-z) * (c d d' ((2 : ℂ) • z))⁻¹ := by sorry
