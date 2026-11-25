-- Prove2me | Theorems.Thm_GlobalTheory_prod_succMin_le_two_pow_div_mul_covolume
-- name    : GlobalTheory.prod_succMin_le_two_pow_div_mul_covolume
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T23:15:18.5048+00:00
-- url     : https://prove2.me/theorems/34acbc00-b715-48d1-8f31-fa38b469e3a4
-- title:
--   Global Theory: prod succ Min le two pow div mul covolume
-- statement:
--   The Global Theory construction uses the prod succ Min le two pow div mul covolume property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/ExistsNeZeroNormSqLeMulCovolumeRpow.lean#L166-L170
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/ExistsNeZeroNormSqLeMulCovolumeRpow.lean#L166-L170

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsLinearIndependentSqrtEqSuccMinQuad
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_LinearIndependentRealOfIntOfDiscrete
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DiscreteTopologySpanOfLinearIndependent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsNeZeroNormSqLeMulCovolumeRpow
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Module Submodule MeasureTheory
open GlobalTheory
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable [MeasurableSpace E] [BorelSpace E]
variable (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]

theorem GlobalTheory.prod_succMin_le_two_pow_div_mul_covolume :
    ∏ i : Fin (finrank ℝ E), succMin L (i + 1) ≤
      2 ^ finrank ℝ E / volume.real (Metric.ball (0 : E) 1) * ZLattice.covolume L := by sorry
