-- Prove2me | Theorems.Thm_GlobalTheory_Cyc_LiftExp_zpow_lt
-- name    : GlobalTheory.Cyc.LiftExp.zpow_lt
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T03:58:13.763753+00:00
-- url     : https://prove2.me/theorems/7efa53a9-8ec3-5fe3-8dbd-12b7dde0cb7d
-- title:
--   Lift Exp: zpow lt
-- statement:
--   The Lift Exp construction uses the zpow lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/PadicNormZpowSubOnePadicValInt.lean#L34-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/PadicNormZpowSubOnePadicValInt.lean#L34-L35

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_HTBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_PadicNormZpowSubOnePadicValInt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc
open GlobalTheory GlobalTheory.Cyc GlobalTheory.Cyc.LiftExp
variable {l : ℕ} [hl : Fact l.Prime]

theorem GlobalTheory.Cyc.LiftExp.zpow_lt {a b : ℤ} (h : a < b) : (l : ℝ) ^ a < (l : ℝ) ^ b := by sorry
