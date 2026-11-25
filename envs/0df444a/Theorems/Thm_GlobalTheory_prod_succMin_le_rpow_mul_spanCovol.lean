-- Prove2me | Theorems.Thm_GlobalTheory_prod_succMin_le_rpow_mul_spanCovol
-- name    : GlobalTheory.prod_succMin_le_rpow_mul_spanCovol
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T23:15:00.857745+00:00
-- url     : https://prove2.me/theorems/98e6f93c-aafd-44eb-82ad-66696bf17d86
-- title:
--   Global Theory: prod succ Min le rpow mul span Covol
-- statement:
--   The Global Theory construction uses the prod succ Min le rpow mul span Covol property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/ExistsNeZeroNormSqLeMulCovolumeRpow.lean#L197-L204
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/ExistsNeZeroNormSqLeMulCovolumeRpow.lean#L197-L204

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
  (L : Submodule ℤ E) [DiscreteTopology L]

theorem GlobalTheory.prod_succMin_le_rpow_mul_spanCovol :
    ∏ i : Fin (finrank ℤ L), succMin L (i + 1) ≤
      (finrank ℤ L : ℝ) ^ ((finrank ℤ L : ℝ) / 2) * spanCovol L := by sorry
