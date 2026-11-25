-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Sobolev_hasOrder_mulRem
-- name    : GroundTheory.Automorphic.Sobolev.hasOrder_mulRem
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T03:14:28.340712+00:00
-- url     : https://prove2.me/theorems/e3ecff83-a7ea-4c6c-bf57-f9dca593e631
-- title:
--   Sobolev: has Order mul Rem
-- statement:
--   The Sobolev construction uses the has Order mul Rem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/EllipticOperators.lean#L90-L94
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/EllipticOperators.lean#L90-L94

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

theorem GroundTheory.Automorphic.Sobolev.hasOrder_mulRem (χ : 𝓢(E, ℂ)) (r : ℝ) : HasOrder (mulRem χ r) (-1) := by sorry
