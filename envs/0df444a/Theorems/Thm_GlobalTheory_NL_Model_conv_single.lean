-- Prove2me | Theorems.Thm_GlobalTheory_NL_Model_conv_single
-- name    : GlobalTheory.NL.Model.conv_single
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T02:47:11.540365+00:00
-- url     : https://prove2.me/theorems/acb9a28a-3508-4e33-a599-bc8eb9be94ef
-- title:
--   Model: conv single
-- statement:
--   The Model construction uses the conv single property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/UnramifiedSubfieldLeCyclotomicExt.lean#L44-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/UnramifiedSubfieldLeCyclotomicExt.lean#L44-L58

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

theorem GlobalTheory.NL.Model.conv_single (e : PowerSeries L) (a : ℤ) (d : M) (k : ℤ) :
    conv e (Pi.single a d : ℤ → M) k =
      if a ≤ k then PowerSeries.coeff (k - a).toNat e • d else 0 := by sorry
