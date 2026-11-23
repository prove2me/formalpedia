-- Prove2me | Theorems.Thm_GlobalTheory_Pat_PolGp_star_single
-- name    : GlobalTheory.Pat.PolGp.star_single
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T16:28:55.931233+00:00
-- url     : https://prove2.me/theorems/edea85b0-e670-43dd-b58b-fc0d95ed3e6c
-- title:
--   Pol Gp: star single
-- statement:
--   The Pol Gp construction uses the star single property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/FiniteCocycles.lean#L392-L396
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/FiniteCocycles.lean#L392-L396

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

theorem GlobalTheory.Pat.PolGp.star_single (j : Φ.O →+* B) (g : G.Γ) (a : B) : star G j (MonoidAlgebra.single g a) =
    MonoidAlgebra.single (G.sig g)⁻¹ (a * j ((G.mu g : Φ.Oˣ) : Φ.O)) := by sorry
