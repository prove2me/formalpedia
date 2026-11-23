-- Prove2me | Theorems.Thm_GlobalTheory_det_gram_eq_normSq_det
-- name    : GlobalTheory.det_gram_eq_normSq_det
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:26:27.581983+00:00
-- url     : https://prove2.me/theorems/f8ace38f-a590-4264-b750-cee6d283b207
-- title:
--   Global Theory: det gram eq norm Sq det
-- statement:
--   The Global Theory construction uses the det gram eq norm Sq det property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/LinearIndependentRealOfIntOfDiscrete.lean#L12-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/LinearIndependentRealOfIntOfDiscrete.lean#L12-L19

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_LinearIndependentRealOfIntOfDiscrete
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped ComplexOrder InnerProductSpace MatrixOrder
open Module Submodule MeasureTheory Matrix
open GlobalTheory
variable {𝕜 : Type*} [RCLike 𝕜] {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem GlobalTheory.det_gram_eq_normSq_det {V : Type*} [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]
    (b : OrthonormalBasis ι 𝕜 V) (v : ι → V) :
    (gram 𝕜 v).det = ((‖b.toBasis.det v‖ ^ 2 : ℝ) : 𝕜) := by sorry
