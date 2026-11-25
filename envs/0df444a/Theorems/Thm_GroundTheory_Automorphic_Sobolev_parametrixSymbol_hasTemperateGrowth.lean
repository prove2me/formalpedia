-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Sobolev_parametrixSymbol_hasTemperateGrowth
-- name    : GroundTheory.Automorphic.Sobolev.parametrixSymbol_hasTemperateGrowth
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T05:19:44.429202+00:00
-- url     : https://prove2.me/theorems/d218ee37-91ea-468a-b53f-f51dd0142f3d
-- title:
--   Sobolev: parametrix Symbol has Temperate Growth
-- statement:
--   The Sobolev construction uses the parametrix Symbol has Temperate Growth property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/EllipticLocal.lean#L43-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/EllipticLocal.lean#L43-L44

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
variable {ι : Type*} [Fintype ι] {m : ℕ} (c : ι → ℂ) (w : ι → Fin m → E)

theorem GroundTheory.Automorphic.Sobolev.parametrixSymbol_hasTemperateGrowth : (symb0 c w).HasTemperateGrowth := by sorry
