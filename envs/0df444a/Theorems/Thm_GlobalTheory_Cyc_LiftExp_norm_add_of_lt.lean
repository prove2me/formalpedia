-- Prove2me | Theorems.Thm_GlobalTheory_Cyc_LiftExp_norm_add_of_lt
-- name    : GlobalTheory.Cyc.LiftExp.norm_add_of_lt
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T03:52:51.745821+00:00
-- url     : https://prove2.me/theorems/da1f884b-9671-48d2-a0e8-cdd8a2a726c9
-- title:
--   Lift Exp: norm add of lt
-- statement:
--   The Lift Exp construction uses the norm add of lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/PadicNormZpowSubOnePadicValInt.lean#L29-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/PadicNormZpowSubOnePadicValInt.lean#L29-L30

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

theorem GlobalTheory.Cyc.LiftExp.norm_add_of_lt {a b : ℚ_[l]} (h : ‖b‖ < ‖a‖) : ‖a + b‖ = ‖a‖ := by sorry
