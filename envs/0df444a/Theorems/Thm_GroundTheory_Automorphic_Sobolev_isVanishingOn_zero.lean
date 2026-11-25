-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Sobolev_isVanishingOn_zero
-- name    : GroundTheory.Automorphic.Sobolev.isVanishingOn_zero
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T01:59:53.800751+00:00
-- url     : https://prove2.me/theorems/0dc21314-3d9a-5f03-a95c-061c5b5ff244
-- title:
--   Sobolev: is Vanishing On zero
-- statement:
--   The Sobolev construction uses the is Vanishing On zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/EllipticOperators.lean#L134-L135
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/EllipticOperators.lean#L134-L135

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

theorem GroundTheory.Automorphic.Sobolev.isVanishingOn_zero (U : Set E) : Distribution.IsVanishingOn (0 : 𝓢'(E, ℂ)) U := by sorry
