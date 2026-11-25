-- Prove2me | Theorems.Thm_GlobalTheory_DiagBlock_coeff_mul_split
-- name    : GlobalTheory.DiagBlock.coeff_mul_split
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T00:46:58.239791+00:00
-- url     : https://prove2.me/theorems/20966c15-74a0-4878-8865-7cf46eecdabc
-- title:
--   Diag Block: coeff mul split
-- statement:
--   The Diag Block construction uses the coeff mul split property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/DetPowDiagonalRowsBlockJetRestrict.lean#L182-L214
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/DetPowDiagonalRowsBlockJetRestrict.lean#L182-L214

import Mathlib
import Definitions.Def_Formalism_DropLevelBounds_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_LeWeightOfCoeffPow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_DetPowDiagonalRowsBlockJetRestrict
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.UnitaryBoundIntegral Formalism.IncomingBounds
open scoped BigOperators
noncomputable section
open GlobalTheory GlobalTheory.DiagBlock

theorem GlobalTheory.DiagBlock.coeff_mul_split {C : Type} [Field C] {σ : Type} (p : σ → Prop)
    (G H : MvPowerSeries σ C)
    (hG : ∀ m, MvPowerSeries.coeff m G ≠ 0 → ∀ x ∈ m.support, p x)
    (hH : ∀ m, MvPowerSeries.coeff m H ≠ 0 → ∀ x ∈ m.support, ¬ p x)
    (a b : σ →₀ ℕ) (ha : ∀ x ∈ a.support, p x) (hb : ∀ x ∈ b.support, ¬ p x) :
    MvPowerSeries.coeff (a + b) (G * H) = MvPowerSeries.coeff a G * MvPowerSeries.coeff b H := by sorry
