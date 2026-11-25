-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Sobolev_rNSymb_bound
-- name    : GroundTheory.Automorphic.Sobolev.rNSymb_bound
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T05:20:18.965964+00:00
-- url     : https://prove2.me/theorems/57a8f221-1e5d-4797-a16e-f926f92e64e1
-- title:
--   Sobolev: r NSymb bound
-- statement:
--   The Sobolev construction uses the r NSymb bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/EllipticLocal.lean#L275-L280
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/EllipticLocal.lean#L275-L280

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

theorem GroundTheory.Automorphic.Sobolev.rNSymb_bound {μ : ℝ} (hμ : 0 < μ) (N : ℕ) (ξ : E) :
    ‖rNSymb c w μ N ξ‖ ≤ (4 ^ m * (1 + (μ * cl ^ 2)⁻¹)) ^ N *
      (1 + ‖ξ‖ ^ 2) ^ (-((2 * m * N : ℕ) : ℝ) / 2) := by sorry
