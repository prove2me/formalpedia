-- Prove2me | Theorems.Thm_GlobalTheory_NL_Model_mem_latSpan_single
-- name    : GlobalTheory.NL.Model.mem_latSpan_single
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T02:46:54.789703+00:00
-- url     : https://prove2.me/theorems/ae81b19e-02e4-4c72-bcd8-d0413b07583a
-- title:
--   Model: mem lat Span single
-- statement:
--   The Model construction uses the mem lat Span single property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/UnramifiedSubfieldLeCyclotomicExt.lean#L103-L122
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/UnramifiedSubfieldLeCyclotomicExt.lean#L103-L122

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

theorem GlobalTheory.NL.Model.mem_latSpan_single (a : ℤ) (f : ℤ → L) :
    f ∈ latSpan (LL := L) (fun _ : Unit => (Pi.single a 1 : ℤ → L)) ↔ ∀ k < a, f k = 0 := by sorry
