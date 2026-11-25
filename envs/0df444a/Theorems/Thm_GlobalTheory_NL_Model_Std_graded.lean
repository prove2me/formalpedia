-- Prove2me | Theorems.Thm_GlobalTheory_NL_Model_Std_graded
-- name    : GlobalTheory.NL.Model.Std.graded
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T12:14:21.593478+00:00
-- url     : https://prove2.me/theorems/70605dd1-0cb9-53fd-8e5b-073fcdf3008e
-- title:
--   Std: graded
-- statement:
--   The Std construction uses the graded property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/UnramifiedSubfieldLeCyclotomicExt.lean#L127-L142
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/UnramifiedSubfieldLeCyclotomicExt.lean#L127-L142

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

theorem GlobalTheory.NL.Model.Std.graded {D : Submodule L M} {Λ : Submodule L (ℤ → M)} (h : Std D Λ) : Graded Λ := by sorry
