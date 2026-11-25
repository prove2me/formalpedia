-- Prove2me | Theorems.Thm_GlobalTheory_NL_Model_line_tests
-- name    : GlobalTheory.NL.Model.line_tests
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T12:14:23.006807+00:00
-- url     : https://prove2.me/theorems/107c3715-1915-56ff-9214-7c141b6b7133
-- title:
--   Model: line tests
-- statement:
--   The Model construction uses the line tests property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/UnramifiedSubfieldLeCyclotomicExt.lean#L144-L169
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/UnramifiedSubfieldLeCyclotomicExt.lean#L144-L169

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_NotFullBot
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnramifiedSubfieldLeCyclotomicExt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.NL GlobalTheory.NL.Model
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.NL
variable {L M : Type} [Field L] [AddCommGroup M] [Module L M]

theorem GlobalTheory.NL.Model.line_tests (a : ℤ) :
    Full (⊤ : Submodule L L) (latSpan (LL := L) (fun _ : Unit => (Pi.single a 1 : ℤ → L))) ∧
    Graded (latSpan (LL := L) (fun _ : Unit => (Pi.single a 1 : ℤ → L))) ∧
    (Std (⊤ : Submodule L L) (latSpan (LL := L) (fun _ : Unit => (Pi.single a 1 : ℤ → L))) ↔ a = 0) := by sorry
