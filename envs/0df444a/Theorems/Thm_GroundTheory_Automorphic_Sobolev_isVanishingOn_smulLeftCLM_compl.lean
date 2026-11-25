-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Sobolev_isVanishingOn_smulLeftCLM_compl
-- name    : GroundTheory.Automorphic.Sobolev.isVanishingOn_smulLeftCLM_compl
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T01:59:47.916342+00:00
-- url     : https://prove2.me/theorems/e6005508-d010-5d5a-9ba8-9fdda321b341
-- title:
--   Sobolev: is Vanishing On smul Left CLM compl
-- statement:
--   The Sobolev construction uses the is Vanishing On smul Left CLM compl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/EllipticOperators.lean#L197-L207
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/EllipticOperators.lean#L197-L207

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

theorem GroundTheory.Automorphic.Sobolev.isVanishingOn_smulLeftCLM_compl {g : E → ℂ} (hg : g.HasTemperateGrowth) (u : 𝓢'(E, ℂ)) :
    Distribution.IsVanishingOn (smulLeftCLM ℂ g u) (tsupport g)ᶜ := by sorry
