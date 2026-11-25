-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Sobolev_isVanishingOn_add
-- name    : GroundTheory.Automorphic.Sobolev.isVanishingOn_add
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T01:59:30.621122+00:00
-- url     : https://prove2.me/theorems/f62febb7-7bad-48e8-9ba0-2250d6481e07
-- title:
--   Sobolev: is Vanishing On add
-- statement:
--   The Sobolev construction uses the is Vanishing On add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/EllipticOperators.lean#L118-L120
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/EllipticOperators.lean#L118-L120

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

theorem GroundTheory.Automorphic.Sobolev.isVanishingOn_add {u v : 𝓢'(E, ℂ)} {U : Set E} (hu : Distribution.IsVanishingOn u U)
    (hv : Distribution.IsVanishingOn v U) : Distribution.IsVanishingOn (u + v) U := by sorry
