-- Prove2me | Theorems.Thm_GlobalTheory_Pat_PolGp_star_star
-- name    : GlobalTheory.Pat.PolGp.star_star
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T12:15:22.976074+00:00
-- url     : https://prove2.me/theorems/664319f5-5020-4d33-8479-c160fe33ed97
-- title:
--   Pol Gp: star star
-- statement:
--   The Pol Gp construction uses the star star property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/FiniteCocycles.lean#L422-L428
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/FiniteCocycles.lean#L422-L428

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

theorem GlobalTheory.Pat.PolGp.star_star (j : Φ.O →+* B) (x : MonoidAlgebra B G.Γ) : star G j (star G j x) = x := by sorry
