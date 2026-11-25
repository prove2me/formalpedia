-- Prove2me | Theorems.Thm_GlobalTheory_UnitCase_mvExp_sum
-- name    : GlobalTheory.UnitCase.mvExp_sum
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T00:41:18.619388+00:00
-- url     : https://prove2.me/theorems/a46dfbe9-2580-426c-a58e-972d1229fb42
-- title:
--   Unit Case: mv Exp sum
-- statement:
--   The Unit Case construction uses the mv Exp sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/LeWeightOfCoeffPow.lean#L89-L96
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/LeWeightOfCoeffPow.lean#L89-L96

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

theorem GlobalTheory.UnitCase.mvExp_sum [CharZero C] {ι : Type} (s : Finset ι) (a : ι → MvPowerSeries σ C)
    (ha : ∀ i, MvPowerSeries.constantCoeff (a i) = 0) :
    mvExp (∑ i ∈ s, a i) = ∏ i ∈ s, mvExp (a i) := by sorry
