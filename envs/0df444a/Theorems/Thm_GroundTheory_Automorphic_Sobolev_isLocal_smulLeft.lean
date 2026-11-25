-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Sobolev_isLocal_smulLeft
-- name    : GroundTheory.Automorphic.Sobolev.isLocal_smulLeft
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T01:59:16.55786+00:00
-- url     : https://prove2.me/theorems/7bdd9f97-86ce-48de-b0cc-f4d58a17b42f
-- title:
--   Sobolev: is Local smul Left
-- statement:
--   The Sobolev construction uses the is Local smul Left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/EllipticOperators.lean#L168-L170
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/EllipticOperators.lean#L168-L170

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

theorem GroundTheory.Automorphic.Sobolev.isLocal_smulLeft {g : E → ℂ} (hg : g.HasTemperateGrowth) :
    IsLocal (smulLeftCLM ℂ g) := by sorry
