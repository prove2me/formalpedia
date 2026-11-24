-- Prove2me | Theorems.Thm_GlobalTheory_hasSum_multilinear_tuples
-- name    : GlobalTheory.hasSum_multilinear_tuples
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T22:54:12.139948+00:00
-- url     : https://prove2.me/theorems/026fc62e-940f-405b-a69a-57848bcc4acf
-- title:
--   Global Theory: has Sum multilinear tuples
-- statement:
--   The Global Theory construction uses the has Sum multilinear tuples property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/SetIntegralPowEqZeroOfPosFreqEuclidean.lean#L32-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/SetIntegralPowEqZeroOfPosFreqEuclidean.lean#L32-L52

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_SummablePiProd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_SetIntegralPowEqZeroOfPosFreqEuclidean
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Topology
open scoped Real FourierTransform Pointwise
open GlobalTheory
variable {ι : Type*} [Fintype ι] {J : ι → Type*}
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {V : ι → Type*} [∀ i, NormedAddCommGroup (V i)]
  [∀ i, NormedSpace 𝕜 (V i)] {W : Type*} [NormedAddCommGroup W] [NormedSpace 𝕜 W]

theorem GlobalTheory.hasSum_multilinear_tuples [CompleteSpace W] (M : ContinuousMultilinearMap 𝕜 V W)
    {x : ∀ i, J i → V i} {A : ∀ i, V i} (hx : ∀ i, Summable fun j => ‖x i j‖)
    (hA : ∀ i, HasSum (x i) (A i)) :
    HasSum (fun t : ∀ i, J i => M fun i => x i (t i)) (M A) := by sorry
