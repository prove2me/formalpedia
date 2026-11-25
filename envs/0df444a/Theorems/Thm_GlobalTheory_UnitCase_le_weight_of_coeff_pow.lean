-- Prove2me | Theorems.Thm_GlobalTheory_UnitCase_le_weight_of_coeff_pow
-- name    : GlobalTheory.UnitCase.le_weight_of_coeff_pow
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T00:40:04.893587+00:00
-- url     : https://prove2.me/theorems/4248ca9a-12c9-454d-8abe-47a12191ab63
-- title:
--   Unit Case: le weight of coeff pow
-- statement:
--   The Unit Case construction uses the le weight of coeff pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/LeWeightOfCoeffPow.lean#L606-L618
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/LeWeightOfCoeffPow.lean#L606-L618

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

theorem GlobalTheory.UnitCase.le_weight_of_coeff_pow (w : (σ →₀ ℕ) → ℕ) (hw : ∀ a b, w (a + b) = w a + w b)
    {h : MvPowerSeries σ C} (hh : ∀ p, MvPowerSeries.coeff p h ≠ 0 → 1 ≤ w p) (k : ℕ) :
    ∀ p, MvPowerSeries.coeff p (h ^ k) ≠ 0 → k ≤ w p := by sorry
