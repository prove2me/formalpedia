-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Sobolev_rhoSymb_mul_sqrt_pow_le
-- name    : GroundTheory.Automorphic.Sobolev.rhoSymb_mul_sqrt_pow_le
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T05:20:52.119462+00:00
-- url     : https://prove2.me/theorems/a494f9ef-39b0-573a-9939-46809adceb19
-- title:
--   Sobolev: rho Symb mul sqrt pow le
-- statement:
--   The Sobolev construction uses the rho Symb mul sqrt pow le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/EllipticLocal.lean#L247-L273
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/EllipticLocal.lean#L247-L273

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
variable {ι : Type*} [Fintype ι] {m : ℕ} (c : ι → ℂ) (w : ι → Fin m → E) {cl Cu : ℝ}
variable (hcl : 0 < cl) (hCu : 0 ≤ Cu) (hlow : ∀ ξ, cl * ‖ξ‖ ^ m ≤ ‖symb0 c w ξ‖)
  (hup : ∀ ξ, ‖symb0 c w ξ‖ ≤ Cu * ‖ξ‖ ^ m)
include hcl hCu hlow hup

theorem GroundTheory.Automorphic.Sobolev.rhoSymb_mul_sqrt_pow_le {μ : ℝ} (hμ : 0 < μ) (ξ : E) :
    ‖rhoSymb c w μ ξ‖ * Real.sqrt (1 + ‖ξ‖ ^ 2) ^ (2 * m) ≤ 4 ^ m * (1 + (μ * cl ^ 2)⁻¹) := by sorry
