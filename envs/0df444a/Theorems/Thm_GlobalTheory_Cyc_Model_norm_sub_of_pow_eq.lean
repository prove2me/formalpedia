-- Prove2me | Theorems.Thm_GlobalTheory_Cyc_Model_norm_sub_of_pow_eq
-- name    : GlobalTheory.Cyc.Model.norm_sub_of_pow_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:31:20.33384+00:00
-- url     : https://prove2.me/theorems/f8f5d912-1dfa-4246-921a-8eab18ff9a42
-- title:
--   Model: norm sub of pow eq
-- statement:
--   The Model construction uses the norm sub of pow eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/PowLtFirstRadius.lean#L150-L162
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/PowLtFirstRadius.lean#L150-L162

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

theorem GlobalTheory.Cyc.Model.norm_sub_of_pow_eq {ζ : Om l} {m a b : ℕ} (hζ : IsPrimitiveRoot ζ (l ^ m)) (h : ζ ^ a = ζ ^ b) :
    ‖(a : ℚ_[l]) - (b : ℚ_[l])‖ ≤ (l : ℝ) ^ (-(m : ℤ)) := by sorry
