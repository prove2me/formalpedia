-- Prove2me | Theorems.Thm_GlobalTheory_UnitCase_constantCoeff_eq_zero
-- name    : GlobalTheory.UnitCase.constantCoeff_eq_zero
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T00:37:06.290816+00:00
-- url     : https://prove2.me/theorems/762d56e0-5408-4ec7-b539-87ba53e0b214
-- title:
--   Unit Case: constant Coeff eq zero
-- statement:
--   The Unit Case construction uses the constant Coeff eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/LeWeightOfCoeffPow.lean#L646-L651
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/LeWeightOfCoeffPow.lean#L646-L651

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

theorem GlobalTheory.UnitCase.constantCoeff_eq_zero {v : AddValuation C (WithTop ℝ)} {l n0 : ℕ}
    {h1 : MvPowerSeries (PVar n0) C} (H : MplusRows v l n0 h1) :
    MvPowerSeries.constantCoeff h1 = 0 := by sorry
