-- Prove2me | Theorems.Thm_GlobalTheory_prod_succMin_le_rpow_mul_covolume
-- name    : GlobalTheory.prod_succMin_le_rpow_mul_covolume
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T15:52:03.410645+00:00
-- url     : https://prove2.me/theorems/f220fd05-f4d6-4d6a-a78f-607f70e9d061
-- title:
--   Global Theory: prod succ Min le rpow mul covolume
-- statement:
--   The Global Theory construction uses the prod succ Min le rpow mul covolume property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/ExistsNeZeroNormSqLeMulCovolumeRpow.lean#L172-L177
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/ExistsNeZeroNormSqLeMulCovolumeRpow.lean#L172-L177

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

theorem GlobalTheory.prod_succMin_le_rpow_mul_covolume :
    ∏ i : Fin (finrank ℝ E), succMin L (i + 1) ≤
      (finrank ℝ E : ℝ) ^ ((finrank ℝ E : ℝ) / 2) * ZLattice.covolume L := by sorry
