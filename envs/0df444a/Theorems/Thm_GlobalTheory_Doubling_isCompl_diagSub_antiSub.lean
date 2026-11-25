-- Prove2me | Theorems.Thm_GlobalTheory_Doubling_isCompl_diagSub_antiSub
-- name    : GlobalTheory.Doubling.isCompl_diagSub_antiSub
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T12:04:05.67553+00:00
-- url     : https://prove2.me/theorems/3751ad28-3ecc-4a77-aae1-fc5792e0f601
-- title:
--   Doubling: is Compl diag Sub anti Sub
-- statement:
--   The Doubling construction uses the is Compl diag Sub anti Sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/MemSiegelOfIffRightAct.lean#L175-L189
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/MemSiegelOfIffRightAct.lean#L175-L189

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsIwasawaOfIsCompact
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MemSiegelOfIffRightAct
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.Doubling
open Matrix Formalism.UG
variable {A B : Type} [CommRing A] [CommRing B] {m n ι : Type}
variable (e : n ⊕ n ≃ ι)

theorem GlobalTheory.Doubling.isCompl_diagSub_antiSub [Invertible (2 : A)] : IsCompl (diagSub A e) (antiSub A e) := by sorry
