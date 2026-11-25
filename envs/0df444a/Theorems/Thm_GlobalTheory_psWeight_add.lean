-- Prove2me | Theorems.Thm_GlobalTheory_psWeight_add
-- name    : GlobalTheory.psWeight_add
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T00:34:31.002906+00:00
-- url     : https://prove2.me/theorems/9542048a-f258-4393-bc14-7a501f85699a
-- title:
--   Global Theory: ps Weight add
-- statement:
--   The Global Theory construction uses the ps Weight add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/PsWeightCalculus.lean#L37-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/PsWeightCalculus.lean#L37-L51

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

theorem GlobalTheory.psWeight_add {C : Type} [Field C] (v : AddValuation C (WithTop ℝ)) {σ : Type}
    (ρ : σ → ℝ) (g g' : MvPowerSeries σ C) (r r' : ℝ)
    (h : ∀ α, (((r) - α.sum (fun j e => ρ j * (e : ℝ)) : ℝ) : WithTop ℝ)
      ≤ v (MvPowerSeries.coeff α g))
    (h' : ∀ α, (((r') - α.sum (fun j e => ρ j * (e : ℝ)) : ℝ) : WithTop ℝ)
      ≤ v (MvPowerSeries.coeff α g')) :
    ∀ α, (((min r r') - α.sum (fun j e => ρ j * (e : ℝ)) : ℝ) : WithTop ℝ)
      ≤ v (MvPowerSeries.coeff α (g + g')) := by sorry
