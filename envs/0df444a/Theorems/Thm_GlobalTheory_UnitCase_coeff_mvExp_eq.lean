-- Prove2me | Theorems.Thm_GlobalTheory_UnitCase_coeff_mvExp_eq
-- name    : GlobalTheory.UnitCase.coeff_mvExp_eq
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T00:36:58.67756+00:00
-- url     : https://prove2.me/theorems/923f1577-f728-44aa-bd5c-9a21e084eb13
-- title:
--   Unit Case: coeff mv Exp eq
-- statement:
--   The Unit Case construction uses the coeff mv Exp eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/LeWeightOfCoeffPow.lean#L22-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/LeWeightOfCoeffPow.lean#L22-L35

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

theorem GlobalTheory.UnitCase.coeff_mvExp_eq {a : MvPowerSeries σ C} (ha : MvPowerSeries.constantCoeff a = 0)
    (m : σ →₀ ℕ) (N : ℕ) (h : m.degree < N) :
    MvPowerSeries.coeff m (mvExp a) =
      ∑ k ∈ Finset.range N, MvPowerSeries.coeff m (a ^ k) / (k.factorial : C) := by sorry
