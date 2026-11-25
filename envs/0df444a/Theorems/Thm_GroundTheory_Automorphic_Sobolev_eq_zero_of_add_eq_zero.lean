-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Sobolev_eq_zero_of_add_eq_zero
-- name    : GroundTheory.Automorphic.Sobolev.eq_zero_of_add_eq_zero
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T05:21:20.44611+00:00
-- url     : https://prove2.me/theorems/4eee04e7-0b34-4425-95c8-efec9fd434e9
-- title:
--   Sobolev: eq zero of add eq zero
-- statement:
--   The Sobolev construction uses the eq zero of add eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/EllipticLocal.lean#L501-L513
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/EllipticLocal.lean#L501-L513

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_EllipticOperators
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_EllipticLocal
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

theorem GroundTheory.Automorphic.Sobolev.eq_zero_of_add_eq_zero {K : 𝓢'(E, ℂ) →L[ℂ] 𝓢'(E, ℂ)} {s : ℝ} (hK : OpBound K s s (1 / 2))
    {v : 𝓢'(E, ℂ)} (hv : MemSobolev s 2 v) (h : v + K v = 0) : v = 0 := by sorry
