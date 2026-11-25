-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Sobolev_constSymb_hasTemperateGrowth
-- name    : GroundTheory.Automorphic.Sobolev.constSymb_hasTemperateGrowth
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T03:54:43.564077+00:00
-- url     : https://prove2.me/theorems/17c3999a-fabc-4085-b8ad-90803ffb6631
-- title:
--   Sobolev: const Symb has Temperate Growth
-- statement:
--   The Sobolev construction uses the const Symb has Temperate Growth property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/EllipticOperators.lean#L408-L415
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/EllipticOperators.lean#L408-L415

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
variable {ι : Type*} [Fintype ι] {m : ℕ} (a : ι → 𝓢(E, ℂ)) (w : ι → Fin m → E)

theorem GroundTheory.Automorphic.Sobolev.constSymb_hasTemperateGrowth (c : ι → ℂ) :
    (fun ξ ↦ (2 * Real.pi * Complex.I) ^ m * prinSymb c w ξ).HasTemperateGrowth := by sorry
