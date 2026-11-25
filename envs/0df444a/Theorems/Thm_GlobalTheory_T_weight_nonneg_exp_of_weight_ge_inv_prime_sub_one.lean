-- Prove2me | Theorems.Thm_GlobalTheory_T_weight_nonneg_exp_of_weight_ge_inv_prime_sub_one
-- name    : GlobalTheory.T.weight_nonneg_exp_of_weight_ge_inv_prime_sub_one
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T00:54:07.282719+00:00
-- url     : https://prove2.me/theorems/2b12dfa9-10a4-4d10-9323-1aecb575dc52
-- title:
--   T: weight nonneg exp of weight ge inv prime sub one
-- statement:
--   The T construction uses the weight nonneg exp of weight ge inv prime sub one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/WeightNonnegExpOfWeightGeInvPrimeSubOneStatement.lean#L8-L10
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/WeightNonnegExpOfWeightGeInvPrimeSubOneStatement.lean#L8-L10

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_WeightNonnegExpOfWeightGeInvPrimeSubOne
import Definitions.Def_ReciprocityTheory_DualLattices_DetPolyMulCayleyOmegaPow
import Definitions.Def_ReciprocityTheory_DualLattices_VEqZeroOfPowEqOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_PeriodValuation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_WeightNonnegExpOfWeightGeInvPrimeSubOneStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.PGsh
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.weight_nonneg_exp_of_weight_ge_inv_prime_sub_one : (∀ (C : Type) [Field C] [CharZero C] (v : AddValuation C (WithTop ℝ)) (l : ℕ), l.Prime → v (l : C) = 1 → ∀ (σ : Type) [Fintype σ] [DecidableEq σ] (ρ : σ → ℝ) (h : MvPowerSeries σ C), MvPowerSeries.constantCoeff h = 0 →
    (∀ α, (((1 / (l - 1)) - α.sum (fun j e => ρ j * (e : ℝ)) : ℝ) : WithTop ℝ) ≤ v (MvPowerSeries.coeff α (h))) → (∀ α, (((0) - α.sum (fun j e => ρ j * (e : ℝ)) : ℝ) : WithTop ℝ) ≤ v (MvPowerSeries.coeff α (PowerSeries.subst (h) (PowerSeries.exp C))))) := by sorry
