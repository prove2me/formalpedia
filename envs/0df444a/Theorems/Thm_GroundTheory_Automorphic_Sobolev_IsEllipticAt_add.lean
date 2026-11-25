-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Sobolev_IsEllipticAt_add
-- name    : GroundTheory.Automorphic.Sobolev.IsEllipticAt.add
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T01:59:01.412574+00:00
-- url     : https://prove2.me/theorems/39ad3232-23a5-5454-ade4-334882c0c3e4
-- title:
--   Is Elliptic At: add
-- statement:
--   The Is Elliptic At construction uses the add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/EllipticOperators.lean#L458-L461
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/EllipticOperators.lean#L458-L461

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevMultiplication
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_EllipticOperators
import Theorems.Thm_GroundTheory_Automorphic_IsHilbertSchmidt_add

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
open GroundTheory.Automorphic.Sobolev.IsEllipticAt
variable {T : 𝓢'(E, ℂ) →L[ℂ] 𝓢'(E, ℂ)} {m : ℕ} {x₀ : E}

theorem GroundTheory.Automorphic.Sobolev.IsEllipticAt.add (h : IsEllipticAt T m x₀) {N' : 𝓢'(E, ℂ) →L[ℂ] 𝓢'(E, ℂ)}
    (hN' : HasOrder N' ((m : ℝ) - 1)) (hL : IsLocal N') : IsEllipticAt (T + N') m x₀ := by sorry
