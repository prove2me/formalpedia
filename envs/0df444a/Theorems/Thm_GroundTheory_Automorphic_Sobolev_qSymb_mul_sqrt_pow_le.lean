-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Sobolev_qSymb_mul_sqrt_pow_le
-- name    : GroundTheory.Automorphic.Sobolev.qSymb_mul_sqrt_pow_le
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T05:20:32.730981+00:00
-- url     : https://prove2.me/theorems/3998069c-b3d3-42f2-86d7-3d4770ae3680
-- title:
--   Sobolev: q Symb mul sqrt pow le
-- statement:
--   The Sobolev construction uses the q Symb mul sqrt pow le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/EllipticLocal.lean#L162-L186
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/EllipticLocal.lean#L162-L186

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

theorem GroundTheory.Automorphic.Sobolev.qSymb_mul_sqrt_pow_le {μ : ℝ} (hμ0 : 0 ≤ μ) (hμ1 : μ ≤ 1) (ξ : E) :
    ‖qSymb c w μ ξ‖ * Real.sqrt (1 + ‖ξ‖ ^ 2) ^ m ≤ 2 ^ m * (cl⁻¹ + Cu) := by sorry
