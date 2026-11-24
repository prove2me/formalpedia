-- Prove2me | Theorems.Thm_GlobalTheory_ThetaTangent_dense_ne_zero
-- name    : GlobalTheory.ThetaTangent.dense_ne_zero
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T05:57:54.055954+00:00
-- url     : https://prove2.me/theorems/1147db81-24f5-4517-9ac3-d859a4a42914
-- title:
--   Theta Tangent: dense ne zero
-- statement:
--   The Theta Tangent construction uses the dense ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/LevelThreeSeparatesTangentVectors.lean#L16-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/LevelThreeSeparatesTangentVectors.lean#L16-L27

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Change
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_LevelThreeSeparatesTangentVectors
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.PTheta Complex Matrix Filter Topology
open scoped BigOperators Real
open GlobalTheory GlobalTheory.ThetaTangent
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem GlobalTheory.ThetaTangent.dense_ne_zero [FiniteDimensional ℂ E] {f : E → ℂ} (hf : Differentiable ℂ f)
    (h0 : f ≠ 0) : Dense {x | f x ≠ 0} := by sorry
