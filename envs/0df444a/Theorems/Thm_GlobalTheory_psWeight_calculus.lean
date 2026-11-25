-- Prove2me | Theorems.Thm_GlobalTheory_psWeight_calculus
-- name    : GlobalTheory.psWeight_calculus
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T00:34:21.283844+00:00
-- url     : https://prove2.me/theorems/1bbc7d81-e749-40b7-a52a-91a0ccba943c
-- title:
--   Global Theory: ps Weight calculus
-- statement:
--   The Global Theory construction uses the ps Weight calculus property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/PsWeightCalculus.lean#L75-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/PsWeightCalculus.lean#L75-L80

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_DetPolyMulCayleyOmegaPow
import Definitions.Def_ReciprocityTheory_DualLattices_VEqZeroOfPowEqOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_PeriodValuation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_PsWeightCalculus
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.PGsh
open GlobalTheory

theorem GlobalTheory.psWeight_calculus :
  (∀ (C : Type) [Field C] (v : AddValuation C (WithTop ℝ)) (σ : Type) [Fintype σ] [DecidableEq σ] (ρ : σ → ℝ) (g g' : MvPowerSeries σ C) (r r' : ℝ),
    (∀ α, (((r) - α.sum (fun j e => ρ j * (e : ℝ)) : ℝ) : WithTop ℝ) ≤ v (MvPowerSeries.coeff α (g))) → ((∀ α, (((r') - α.sum (fun j e => ρ j * (e : ℝ)) : ℝ) : WithTop ℝ) ≤ v (MvPowerSeries.coeff α (g'))) → (∀ α, (((r + r') - α.sum (fun j e => ρ j * (e : ℝ)) : ℝ) : WithTop ℝ) ≤ v (MvPowerSeries.coeff α (g * g'))) ∧ (∀ α, (((min r r') - α.sum (fun j e => ρ j * (e : ℝ)) : ℝ) : WithTop ℝ) ≤ v (MvPowerSeries.coeff α (g + g')))) ∧ ∀ N : ℕ, (∀ α, (((N * r) - α.sum (fun j e => ρ j * (e : ℝ)) : ℝ) : WithTop ℝ) ≤ v (MvPowerSeries.coeff α (g ^ N)))) := by sorry
