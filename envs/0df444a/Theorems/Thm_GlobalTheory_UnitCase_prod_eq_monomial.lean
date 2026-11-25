-- Prove2me | Theorems.Thm_GlobalTheory_UnitCase_prod_eq_monomial
-- name    : GlobalTheory.UnitCase.prod_eq_monomial
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T00:39:50.016799+00:00
-- url     : https://prove2.me/theorems/eef4f7da-109f-4d9d-9792-8635d4cc1023
-- title:
--   Unit Case: prod eq monomial
-- statement:
--   The Unit Case construction uses the prod eq monomial property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/LeWeightOfCoeffPow.lean#L167-L187
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/LeWeightOfCoeffPow.lean#L167-L187

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

theorem GlobalTheory.UnitCase.prod_eq_monomial [Fintype κ] (l : ℕ) (B : κ →₀ ℕ) :
    ∏ j, ((MvPowerSeries.X (Sum.inl j) : MvPowerSeries (κ ⊕ κ) C) ^ l *
      MvPowerSeries.X (Sum.inr j)) ^ (B j) =
      MvPowerSeries.monomial (Finsupp.sumElim (l • B) B) 1 := by sorry
