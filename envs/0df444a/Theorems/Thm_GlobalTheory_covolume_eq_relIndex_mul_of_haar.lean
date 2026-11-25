-- Prove2me | Theorems.Thm_GlobalTheory_covolume_eq_relIndex_mul_of_haar
-- name    : GlobalTheory.covolume_eq_relIndex_mul_of_haar
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T04:08:37.987863+00:00
-- url     : https://prove2.me/theorems/824aa75e-fc81-4d35-9fec-e2389e392159
-- title:
--   Global Theory: covolume eq rel Index mul of haar
-- statement:
--   The Global Theory construction uses the covolume eq rel Index mul of haar property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/ExistsNeZeroForallNormLeOfCovolumeLe.lean#L20-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/ExistsNeZeroForallNormLeOfCovolumeLe.lean#L20-L35

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsNeZeroMemFractionalIdealNormSqLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FinrankMulDiscrRpowLeSumSqOfMemTraceDual
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsIdealInClassOfNormLeSqrtDiscr
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EnormPowLeInvMeasureMulLintegralBall
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsNeZeroForallNormLeOfCovolumeLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module MeasureTheory Metric Set
open scoped Real ENNReal
open GlobalTheory
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
variable [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure]
set_option backward.isDefEq.respectTransparency.types false

theorem GlobalTheory.covolume_eq_relIndex_mul_of_haar (L' L : Submodule ℤ V) [DiscreteTopology L']
    [IsZLattice ℝ L'] [DiscreteTopology L] [IsZLattice ℝ L] (h : L' ≤ L) :
    ZLattice.covolume L' μ =
      (L'.toAddSubgroup.relIndex L.toAddSubgroup : ℝ) * ZLattice.covolume L μ := by sorry
