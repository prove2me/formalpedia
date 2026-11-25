-- Prove2me | Theorems.Thm_GlobalTheory_UnitCase_coeff_mul_pow_eq_zero
-- name    : GlobalTheory.UnitCase.coeff_mul_pow_eq_zero
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T00:36:48.409987+00:00
-- url     : https://prove2.me/theorems/abb39e1c-8e3d-4097-8c46-17f076a2a63b
-- title:
--   Unit Case: coeff mul pow eq zero
-- statement:
--   The Unit Case construction uses the coeff mul pow eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/LeWeightOfCoeffPow.lean#L13-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/LeWeightOfCoeffPow.lean#L13-L20

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

theorem GlobalTheory.UnitCase.coeff_mul_pow_eq_zero {a b : MvPowerSeries σ C} (ha : MvPowerSeries.constantCoeff a = 0)
    (hb : MvPowerSeries.constantCoeff b = 0) (j k : ℕ) (m : σ →₀ ℕ) (h : m.degree < j + k) :
    MvPowerSeries.coeff m (a ^ j * b ^ k) = 0 := by sorry
