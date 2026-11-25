-- Prove2me | Theorems.Thm_GlobalTheory_ExpWeight_weight_exp
-- name    : GlobalTheory.ExpWeight.weight_exp
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T00:38:59.912652+00:00
-- url     : https://prove2.me/theorems/ebc276d5-5712-4399-bee0-5ebbcd7a08ee
-- title:
--   Exp Weight: weight exp
-- statement:
--   The Exp Weight construction uses the weight exp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/WeightNonnegExpOfWeightGeInvPrimeSubOne.lean#L17-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/WeightNonnegExpOfWeightGeInvPrimeSubOne.lean#L17-L78

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_DetPolyMulCayleyOmegaPow
import Definitions.Def_ReciprocityTheory_DualLattices_VEqZeroOfPowEqOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_PeriodValuation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_LegendreBoundsFactorialMultiIndexCapelli
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_WeightNonnegExpOfWeightGeInvPrimeSubOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.PGsh
open GlobalTheory GlobalTheory.ExpWeight
variable {C : Type} [Field C] (v : AddValuation C (WithTop ℝ))
  {σ : Type} [DecidableEq σ] (ρ : σ → ℝ)
variable {C : Type} [Field C] (v : AddValuation C (WithTop ℝ))
  {σ : Type} [DecidableEq σ] (ρ : σ → ℝ)

theorem GlobalTheory.ExpWeight.weight_exp :
  (∀ (C : Type) [Field C] [CharZero C] (v : AddValuation C (WithTop ℝ)) (l : ℕ), l.Prime → v (l : C) = 1 → ∀ (σ : Type) [Fintype σ] [DecidableEq σ] (ρ : σ → ℝ) (h : MvPowerSeries σ C), MvPowerSeries.constantCoeff h = 0 →
    (∀ α, (((1 / (l - 1)) - α.sum (fun j e => ρ j * (e : ℝ)) : ℝ) : WithTop ℝ) ≤ v (MvPowerSeries.coeff α (h))) → (∀ α, (((0) - α.sum (fun j e => ρ j * (e : ℝ)) : ℝ) : WithTop ℝ) ≤ v (MvPowerSeries.coeff α (PowerSeries.subst (h) (PowerSeries.exp C))))) := by sorry
