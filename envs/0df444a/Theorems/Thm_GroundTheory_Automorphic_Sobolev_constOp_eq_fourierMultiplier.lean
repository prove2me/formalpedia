-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Sobolev_constOp_eq_fourierMultiplier
-- name    : GroundTheory.Automorphic.Sobolev.constOp_eq_fourierMultiplier
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T03:13:59.313603+00:00
-- url     : https://prove2.me/theorems/45b7d76a-d2f6-486f-a193-17adfd29326e
-- title:
--   Sobolev: const Op eq fourier Multiplier
-- statement:
--   The Sobolev construction uses the const Op eq fourier Multiplier property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/EllipticOperators.lean#L417-L433
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/EllipticOperators.lean#L417-L433

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

theorem GroundTheory.Automorphic.Sobolev.constOp_eq_fourierMultiplier (c : ι → ℂ) :
    constOp w c = fourierMultiplierCLM ℂ (fun ξ ↦ (2 * Real.pi * Complex.I) ^ m * prinSymb c w ξ) := by sorry
