-- Prove2me | Theorems.Thm_GlobalTheory_Prism_Obj_crys_quot_nontrivial
-- name    : GlobalTheory.Prism.Obj.crys_quot_nontrivial
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T12:17:12.78021+00:00
-- url     : https://prove2.me/theorems/fb987062-e1ba-556b-ba3c-e329a13c6a3a
-- title:
--   Obj: crys quot nontrivial
-- statement:
--   The Obj construction uses the crys quot nontrivial property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/InvertibleSpanSingleton.lean#L266-L270
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/InvertibleSpanSingleton.lean#L266-L270

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_InvertibleSpanSingleton
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.Prism
attribute [instance] Obj.ring
variable {l : ℕ} {R : Type} [CommRing R]
attribute [instance] FCrys.acg FCrys.mod
attribute [instance] VBun.acg VBun.mod

theorem GlobalTheory.Prism.Obj.crys_quot_nontrivial (l : ℕ) [Fact l.Prime] :
    Nontrivial ((Obj.crys l).A ⧸ (Obj.crys l).I) := by sorry
