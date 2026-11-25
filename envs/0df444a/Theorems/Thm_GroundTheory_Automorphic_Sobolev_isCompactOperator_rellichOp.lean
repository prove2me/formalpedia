-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Sobolev_isCompactOperator_rellichOp
-- name    : GroundTheory.Automorphic.Sobolev.isCompactOperator_rellichOp
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T03:14:24.659363+00:00
-- url     : https://prove2.me/theorems/4dc4e36f-6378-433a-8f9c-5d75363431c0
-- title:
--   Sobolev: is Compact Operator rellich Op
-- statement:
--   The Sobolev construction uses the is Compact Operator rellich Op property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/SobolevRellich.lean#L179-L181
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/SobolevRellich.lean#L179-L181

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevInterpolation
import Definitions.Def_GroundTheory_AutomorphicForms_HilbertSchmidtKernel
import Definitions.Def_GroundTheory_AutomorphicForms_HilbertSchmidtCompact
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevRellich
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic GroundTheory.Automorphic.Sobolev
open TemperedDistribution MeasureTheory FourierTransform
open scoped SchwartzMap ENNReal ContDiff
noncomputable section
set_option linter.unusedSectionVars false
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
variable {s N : ℝ} (χ : 𝓢(E, ℂ))

theorem GroundTheory.Automorphic.Sobolev.isCompactOperator_rellichOp (hN : (Module.finrank ℝ E : ℝ) < 2 * N) :
    IsCompactOperator (rellichOp (s := s) χ hN) := by sorry
