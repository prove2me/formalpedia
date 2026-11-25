-- Prove2me | Theorems.Thm_GlobalTheory_UnitCase_jetAt0_sum
-- name    : GlobalTheory.UnitCase.jetAt0_sum
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T00:39:51.772142+00:00
-- url     : https://prove2.me/theorems/dd37545e-8851-4e00-bfb3-5e781f60907d
-- title:
--   Unit Case: jet At0 sum
-- statement:
--   The Unit Case construction uses the jet At0 sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/LeWeightOfCoeffPow.lean#L415-L420
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/LeWeightOfCoeffPow.lean#L415-L420

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

theorem GlobalTheory.UnitCase.jetAt0_sum {α : Type} (s : Finset α) (P : α → MvPolynomial σ C) (G : MvPowerSeries σ C) :
    jetAt0 (∑ a ∈ s, P a) G = ∑ a ∈ s, jetAt0 (P a) G := by sorry
