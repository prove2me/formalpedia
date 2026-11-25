-- Prove2me | Theorems.Thm_GroundTheory_GroupCoh_comp_cancel_of_isos
-- name    : GroundTheory.GroupCoh.comp_cancel_of_isos
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T04:34:51.445618+00:00
-- url     : https://prove2.me/theorems/4b03cc1c-5106-599c-a88a-43f0af9cdecc
-- title:
--   Group Coh: comp cancel of isos
-- statement:
--   The Group Coh construction uses the comp cancel of isos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/ResCoresPos.lean#L184-L189
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/ResCoresPos.lean#L184-L189

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_ResCores
import Definitions.Def_GroundTheory_TateCohomology_ResCoresPos
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.GroupCoh
open CategoryTheory Limits Rep groupCohomology
universe u

theorem GroundTheory.GroupCoh.comp_cancel_of_isos {C : Type*} [Category C] {X X' Y Y' Z Z' : C} (pG : X ≅ X') (pS : Y ≅ Y')
    (pGc : Z ≅ Z') (a : X ⟶ Z) (cu : X' ⟶ Z') (m : X' ⟶ Y') (sh : Y' ⟶ Z') (b : Y ⟶ Z) (c : Z ⟶ Y)
    (ha : a = pG.hom ≫ cu ≫ pGc.inv) (hcu : cu = m ≫ sh) (hsh : sh = pS.inv ≫ b ≫ pGc.hom)
    (hb : b ≫ c = 𝟙 Y) : a ≫ c ≫ pS.hom = pG.hom ≫ m := by sorry
