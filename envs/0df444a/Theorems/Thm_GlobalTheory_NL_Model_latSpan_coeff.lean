-- Prove2me | Theorems.Thm_GlobalTheory_NL_Model_latSpan_coeff
-- name    : GlobalTheory.NL.Model.latSpan_coeff
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T02:47:12.722911+00:00
-- url     : https://prove2.me/theorems/8f578505-d8b3-46d1-bef7-1b3bb258c0d3
-- title:
--   Model: lat Span coeff
-- statement:
--   The Model construction uses the lat Span coeff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/UnramifiedSubfieldLeCyclotomicExt.lean#L83-L101
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/UnramifiedSubfieldLeCyclotomicExt.lean#L83-L101

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
open TensorProduct
variable {L M : Type} [Field L] [AddCommGroup M] [Module L M]

theorem GlobalTheory.NL.Model.latSpan_coeff {ι : Type} (ex : ι → ℤ → M)
    (D : Submodule L M) (hD : ∀ x k, ex x k ∈ D) (hs : ∀ x, ∃ m : ℤ, ∀ k < m, ex x k = 0)
    (f : ℤ → M) (hf : f ∈ _root_.GlobalTheory.NL.latSpan (LL := L) ex) :
    (∀ k, f k ∈ D) ∧ ∃ m : ℤ, ∀ k < m, f k = 0 := by sorry
