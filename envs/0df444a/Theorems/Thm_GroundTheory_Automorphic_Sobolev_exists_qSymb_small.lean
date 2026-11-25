-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Sobolev_exists_qSymb_small
-- name    : GroundTheory.Automorphic.Sobolev.exists_qSymb_small
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T05:21:33.478442+00:00
-- url     : https://prove2.me/theorems/e5f73ec3-574d-4939-ab80-c351e0d873fb
-- title:
--   Sobolev: exists q Symb small
-- statement:
--   The Sobolev construction uses the exists q Symb small property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/EllipticLocal.lean#L198-L245
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/EllipticLocal.lean#L198-L245

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

theorem GroundTheory.Automorphic.Sobolev.exists_qSymb_small (hm : 1 ≤ m) {ε : ℝ} (hε : 0 < ε) :
    ∃ μ : ℝ, 0 < μ ∧ μ ≤ 1 ∧ ∀ ξ : E, ‖qSymb c w μ ξ‖ * Real.sqrt (1 + ‖ξ‖ ^ 2) ^ (m - 1) ≤ ε := by sorry
