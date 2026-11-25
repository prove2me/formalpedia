-- Prove2me | Theorems.Thm_GlobalTheory_UnitCase_coeff_zero_mvExp
-- name    : GlobalTheory.UnitCase.coeff_zero_mvExp
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T00:40:14.264046+00:00
-- url     : https://prove2.me/theorems/f67dcca1-2ce8-437f-84a2-d01d97943a16
-- title:
--   Unit Case: coeff zero mv Exp
-- statement:
--   The Unit Case construction uses the coeff zero mv Exp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/LeWeightOfCoeffPow.lean#L79-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/LeWeightOfCoeffPow.lean#L79-L81

import Mathlib
import Definitions.Def_Formalism_DropLevelBounds_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_WtAddSingle
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_LeWeightOfCoeffPow
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.UnitaryBoundIntegral Formalism.IncomingBounds ReciprocityTheory.PGsh
open scoped BigOperators
noncomputable section
open GlobalTheory GlobalTheory.UnitCase
variable {C : Type} [Field C] {σ κ : Type}

theorem GlobalTheory.UnitCase.coeff_zero_mvExp (a : MvPowerSeries σ C) : MvPowerSeries.coeff 0 (mvExp a) = 1 := by sorry
