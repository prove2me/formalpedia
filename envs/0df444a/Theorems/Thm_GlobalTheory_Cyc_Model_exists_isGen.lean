-- Prove2me | Theorems.Thm_GlobalTheory_Cyc_Model_exists_isGen
-- name    : GlobalTheory.Cyc.Model.exists_isGen
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T12:34:27.282049+00:00
-- url     : https://prove2.me/theorems/4d606e57-159e-4f46-a8e2-cc2c6aeb9f05
-- title:
--   Model: exists is Gen
-- statement:
--   The Model construction uses the exists is Gen property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/PowLtFirstRadius.lean#L164-L203
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/PowLtFirstRadius.lean#L164-L203

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

theorem GlobalTheory.Cyc.Model.exists_isGen {χ : GQ l →* ℚ_[l]ˣ} (hχ : IsCyc χ) {j : ℕ} (hj : 1 ≤ j) :
    ∃ g, IsGen χ (base l) j g := by sorry
