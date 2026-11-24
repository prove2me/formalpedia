-- Prove2me | Theorems.Thm_GlobalTheory_ThetaRational_differentiable_of_mem_adjoin
-- name    : GlobalTheory.ThetaRational.differentiable_of_mem_adjoin
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T21:06:37.484436+00:00
-- url     : https://prove2.me/theorems/7f8278c6-579d-4b43-9563-a5cc5beaa184
-- title:
--   Theta Rational: differentiable of mem adjoin
-- statement:
--   The Theta Rational construction uses the differentiable of mem adjoin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/IsIntegralAndRationalTheta.lean#L357-L363
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/IsIntegralAndRationalTheta.lean#L357-L363

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Change
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_IsIntegralAndRationalTheta
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.PTheta Complex Matrix Filter Topology
open scoped BigOperators Real ContDiff
open GlobalTheory GlobalTheory.ThetaRational
variable {E ι : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E] [Fintype ι]
omit [FiniteDimensional ℂ E] [Fintype ι]

theorem GlobalTheory.ThetaRational.differentiable_of_mem_adjoin {u : ι → E → ℂ} (hu : ∀ c, Differentiable ℂ (u c))
    {b : E → ℂ} (hb : b ∈ Algebra.adjoin ℂ (Set.range u)) : Differentiable ℂ b := by sorry
