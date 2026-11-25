-- Prove2me | Theorems.Thm_GlobalTheory_Pat_PolGp_star_mul
-- name    : GlobalTheory.Pat.PolGp.star_mul
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T12:15:41.652323+00:00
-- url     : https://prove2.me/theorems/c668f55b-f96e-4f33-b9ec-83d5e392d70c
-- title:
--   Pol Gp: star mul
-- statement:
--   The Pol Gp construction uses the star mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/FiniteCocycles.lean#L408-L420
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/FiniteCocycles.lean#L408-L420

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FiniteCocycles
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open TensorProduct Polynomial IsLocalRing
noncomputable section
open IsLocalRing
open GlobalTheory GlobalTheory.Pat
attribute [instance] PG.grp PG.top PG.tgrp PG.cpt PG.t2 PG.td
attribute [instance] Frame.hl Frame.iO Frame.iOd Frame.iOv Frame.iVl Frame.iSt
variable {Φ : Frame} (G : PolGp Φ) {B : Type} [CommRing B]

theorem GlobalTheory.Pat.PolGp.star_mul (j : Φ.O →+* B) (x y : MonoidAlgebra B G.Γ) : star G j (x * y) = star G j y * star G j x := by sorry
