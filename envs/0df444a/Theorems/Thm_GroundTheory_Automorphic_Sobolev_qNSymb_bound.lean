-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Sobolev_qNSymb_bound
-- name    : GroundTheory.Automorphic.Sobolev.qNSymb_bound
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T05:21:31.141604+00:00
-- url     : https://prove2.me/theorems/9dfae9ef-ccbc-4639-9bfa-5f4107a3d8b3
-- title:
--   Sobolev: q NSymb bound
-- statement:
--   The Sobolev construction uses the q NSymb bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/EllipticLocal.lean#L188-L196
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/EllipticLocal.lean#L188-L196

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

theorem GroundTheory.Automorphic.Sobolev.qNSymb_bound {μ : ℝ} (hμ0 : 0 ≤ μ) (hμ1 : μ ≤ 1) (N : ℕ) (ξ : E) :
    ‖qNSymb c w μ N ξ‖ ≤ (N * (2 ^ m * (cl⁻¹ + Cu))) * (1 + ‖ξ‖ ^ 2) ^ (-(m : ℝ) / 2) := by sorry
