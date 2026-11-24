-- Prove2me | Theorems.Thm_GlobalTheory_Cyc_Model_pow_lt_first_radius
-- name    : GlobalTheory.Cyc.Model.pow_lt_first_radius
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T12:34:28.681864+00:00
-- url     : https://prove2.me/theorems/4b529277-22ef-40b2-bb92-716a54f88592
-- title:
--   Model: pow lt first radius
-- statement:
--   The Model construction uses the pow lt first radius property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/PowLtFirstRadius.lean#L224-L237
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/PowLtFirstRadius.lean#L224-L237

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

theorem GlobalTheory.Cyc.Model.pow_lt_first_radius {m : ℕ} (h : Lev l m) : (l : ℝ) ^ (-(m : ℤ)) < rho1 l := by sorry
