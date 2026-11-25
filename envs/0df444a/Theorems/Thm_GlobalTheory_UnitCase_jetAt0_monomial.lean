-- Prove2me | Theorems.Thm_GlobalTheory_UnitCase_jetAt0_monomial
-- name    : GlobalTheory.UnitCase.jetAt0_monomial
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T00:40:08.214566+00:00
-- url     : https://prove2.me/theorems/5873c26a-55cc-4fa5-88b5-e0d366f83745
-- title:
--   Unit Case: jet At0 monomial
-- statement:
--   The Unit Case construction uses the jet At0 monomial property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/LeWeightOfCoeffPow.lean#L422-L426
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/LeWeightOfCoeffPow.lean#L422-L426

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

theorem GlobalTheory.UnitCase.jetAt0_monomial (m : σ →₀ ℕ) (c : C) (G : MvPowerSeries σ C) :
    jetAt0 (MvPolynomial.monomial m c) G = c * (mfact m : C) * MvPowerSeries.coeff m G := by sorry
