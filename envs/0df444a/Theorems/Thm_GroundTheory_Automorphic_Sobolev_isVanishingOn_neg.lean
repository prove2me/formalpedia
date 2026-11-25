-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Sobolev_isVanishingOn_neg
-- name    : GroundTheory.Automorphic.Sobolev.isVanishingOn_neg
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T01:59:37.52624+00:00
-- url     : https://prove2.me/theorems/e14e1cfa-72bc-4dc4-8c59-b155e38ec6e9
-- title:
--   Sobolev: is Vanishing On neg
-- statement:
--   The Sobolev construction uses the is Vanishing On neg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/EllipticOperators.lean#L126-L128
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/EllipticOperators.lean#L126-L128

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

theorem GroundTheory.Automorphic.Sobolev.isVanishingOn_neg {u : 𝓢'(E, ℂ)} {U : Set E} (hu : Distribution.IsVanishingOn u U) :
    Distribution.IsVanishingOn (-u) U := by sorry
