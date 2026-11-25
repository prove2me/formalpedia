-- Prove2me | Theorems.Thm_GlobalTheory_Cyc_LiftExp_one_lt_l
-- name    : GlobalTheory.Cyc.LiftExp.one_lt_l
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T03:51:11.051603+00:00
-- url     : https://prove2.me/theorems/fb6a1eca-b7c2-474d-9d70-57bda042c890
-- title:
--   Lift Exp: one lt l
-- statement:
--   The Lift Exp construction uses the one lt l property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/PadicNormZpowSubOnePadicValInt.lean#L32-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/PadicNormZpowSubOnePadicValInt.lean#L32-L32

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

theorem GlobalTheory.Cyc.LiftExp.one_lt_l : (1 : ℝ) < l := by sorry
