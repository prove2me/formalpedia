-- Prove2me | Theorems.Thm_GlobalTheory_succMin_mul_minNorm_pow_le
-- name    : GlobalTheory.succMin_mul_minNorm_pow_le
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T23:22:37.006813+00:00
-- url     : https://prove2.me/theorems/48383378-6e40-49e4-ab7f-98893a731ca2
-- title:
--   Global Theory: succ Min mul min Norm pow le
-- statement:
--   The Global Theory construction uses the succ Min mul min Norm pow le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/ExistsNeZeroNormSqLeMulCovolumeRpow.lean#L179-L188
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/ExistsNeZeroNormSqLeMulCovolumeRpow.lean#L179-L188

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

theorem GlobalTheory.succMin_mul_minNorm_pow_le {k : ℕ} (h1 : 1 ≤ k) (hk : k ≤ finrank ℝ E) :
    succMin L k * minNorm L ^ (finrank ℝ E - 1) ≤
      (finrank ℝ E : ℝ) ^ ((finrank ℝ E : ℝ) / 2) * ZLattice.covolume L := by sorry
