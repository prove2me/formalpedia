-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Sobolev_rhoSymb_hasTemperateGrowth
-- name    : GroundTheory.Automorphic.Sobolev.rhoSymb_hasTemperateGrowth
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T05:20:01.701621+00:00
-- url     : https://prove2.me/theorems/0b754437-0c8b-4692-a21f-39f424d20877
-- title:
--   Sobolev: rho Symb has Temperate Growth
-- statement:
--   The Sobolev construction uses the rho Symb has Temperate Growth property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/EllipticLocal.lean#L58-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/EllipticLocal.lean#L58-L60

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

theorem GroundTheory.Automorphic.Sobolev.rhoSymb_hasTemperateGrowth (μ : ℝ) : (rhoSymb c w μ).HasTemperateGrowth := by sorry
