-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Sobolev_IsEllipticAt_hasOrder_comm
-- name    : GroundTheory.Automorphic.Sobolev.IsEllipticAt.hasOrder_comm
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T02:00:28.262353+00:00
-- url     : https://prove2.me/theorems/e1026f94-408e-4d65-8d7c-d62f9592b5b6
-- title:
--   Is Elliptic At: has Order comm
-- statement:
--   The Is Elliptic At construction uses the has Order comm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/EllipticOperators.lean#L450-L456
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/EllipticOperators.lean#L450-L456

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
open GroundTheory.Automorphic.Sobolev.IsEllipticAt
variable {T : 𝓢'(E, ℂ) →L[ℂ] 𝓢'(E, ℂ)} {m : ℕ} {x₀ : E}

theorem GroundTheory.Automorphic.Sobolev.IsEllipticAt.hasOrder_comm (h : IsEllipticAt T m x₀) (ψ : 𝓢(E, ℂ)) : HasOrder (comm T ψ) ((m : ℝ) - 1) := by sorry
