-- Prove2me | Theorems.Thm_GlobalTheory_hasFDerivAt_Hf_left
-- name    : GlobalTheory.hasFDerivAt_Hf_left
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T22:53:51.302132+00:00
-- url     : https://prove2.me/theorems/116af1f6-de84-4787-a74a-4bd3511f0a23
-- title:
--   Global Theory: has FDeriv At Hf left
-- statement:
--   The Global Theory construction uses the has FDeriv At Hf left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/LevelThreeSeparatesTangents.lean#L99-L106
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/LevelThreeSeparatesTangents.lean#L99-L106

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_LevelThreeSeparatesTangents
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex ReciprocityTheory.ChartRestriction.G.I2 Filter Topology
open GlobalTheory
variable {ι : Type} [Fintype ι]

theorem GlobalTheory.hasFDerivAt_Hf_left (γ v : EuclideanSpace ℂ ι) :
    ∃ A : EuclideanSpace ℂ ι →L[ℂ] ℂ, (∀ c, A c = Hf c γ) ∧ HasFDerivAt (fun v => Hf v γ) A v := by sorry
