-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Sobolev_comm_sum
-- name    : GroundTheory.Automorphic.Sobolev.comm_sum
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T03:13:22.731416+00:00
-- url     : https://prove2.me/theorems/4b16f2ac-4c08-44b9-aa49-eea2f9b9fbd5
-- title:
--   Sobolev: comm sum
-- statement:
--   The Sobolev construction uses the comm sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/EllipticOperators.lean#L262-L267
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/EllipticOperators.lean#L262-L267

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevMultiplication
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_EllipticOperators
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic GroundTheory.Automorphic.Sobolev
open TemperedDistribution MeasureTheory FourierTransform LineDeriv
open scoped SchwartzMap ENNReal ContDiff
noncomputable section
set_option linter.unusedSectionVars false
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

theorem GroundTheory.Automorphic.Sobolev.comm_sum {ι : Type*} (S : Finset ι) (A : ι → 𝓢'(E, ℂ) →L[ℂ] 𝓢'(E, ℂ)) (ψ : 𝓢(E, ℂ)) :
    comm (∑ i ∈ S, A i) ψ = ∑ i ∈ S, comm (A i) ψ := by sorry
