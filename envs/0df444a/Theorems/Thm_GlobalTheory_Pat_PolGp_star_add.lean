-- Prove2me | Theorems.Thm_GlobalTheory_Pat_PolGp_star_add
-- name    : GlobalTheory.Pat.PolGp.star_add
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:29:14.508017+00:00
-- url     : https://prove2.me/theorems/648adb9b-0dfd-4b87-823e-005a5d101e37
-- title:
--   Pol Gp: star add
-- statement:
--   The Pol Gp construction uses the star add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/FiniteCocycles.lean#L402-L406
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/FiniteCocycles.lean#L402-L406

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

theorem GlobalTheory.Pat.PolGp.star_add (j : Φ.O →+* B) (x y : MonoidAlgebra B G.Γ) : star G j (x + y) = star G j x + star G j y := by sorry
