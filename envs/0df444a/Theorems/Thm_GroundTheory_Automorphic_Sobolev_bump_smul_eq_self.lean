-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Sobolev_bump_smul_eq_self
-- name    : GroundTheory.Automorphic.Sobolev.bump_smul_eq_self
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T05:20:27.451555+00:00
-- url     : https://prove2.me/theorems/a7afcd8f-1cb6-4d51-8e05-98d8b763c644
-- title:
--   Sobolev: bump smul eq self
-- statement:
--   The Sobolev construction uses the bump smul eq self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/EllipticLocal.lean#L331-L338
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/EllipticLocal.lean#L331-L338

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

theorem GroundTheory.Automorphic.Sobolev.bump_smul_eq_self (x₀ : E) {r ρ : ℝ} (hr : 0 < r) (hρ : ρ < r) {z : 𝓢'(E, ℂ)}
    (hz : Distribution.IsVanishingOn z (Metric.closedBall x₀ ρ)ᶜ) :
    smulLeftCLM ℂ (bump x₀ hr : E → ℂ) z = z := by sorry
