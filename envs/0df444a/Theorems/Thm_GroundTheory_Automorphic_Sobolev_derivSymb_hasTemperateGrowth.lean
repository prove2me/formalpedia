-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Sobolev_derivSymb_hasTemperateGrowth
-- name    : GroundTheory.Automorphic.Sobolev.derivSymb_hasTemperateGrowth
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T02:00:06.147898+00:00
-- url     : https://prove2.me/theorems/480566e2-175c-4501-accf-108201920403
-- title:
--   Sobolev: deriv Symb has Temperate Growth
-- statement:
--   The Sobolev construction uses the deriv Symb has Temperate Growth property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/EllipticOperators.lean#L293-L303
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/EllipticOperators.lean#L293-L303

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

theorem GroundTheory.Automorphic.Sobolev.derivSymb_hasTemperateGrowth {k : ℕ} (w : Fin k → E) : (derivSymb w).HasTemperateGrowth := by sorry
