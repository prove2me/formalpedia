-- Prove2me | Theorems.Thm_GlobalTheory_Cyc_Model_isActC_unique
-- name    : GlobalTheory.Cyc.Model.isActC_unique
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T12:03:22.381288+00:00
-- url     : https://prove2.me/theorems/2f7b1ceb-fc86-4134-808b-eafde3937073
-- title:
--   Model: is Act C unique
-- statement:
--   The Model construction uses the is Act C unique property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/PowLtFirstRadius.lean#L308-L314
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/PowLtFirstRadius.lean#L308-L314

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_HTBasis
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_PowLtFirstRadius
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.Cyc GlobalTheory.Cyc.Model
open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc Polynomial
variable {l : ℕ} [Fact l.Prime]

theorem GlobalTheory.Cyc.Model.isActC_unique {a b : GQ l →* (PadicComplex l ≃+* PadicComplex l)} (ha : IsActC a)
    (hb : IsActC b) : a = b := by sorry
