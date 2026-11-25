-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Sobolev_opBound_Qop_small
-- name    : GroundTheory.Automorphic.Sobolev.opBound_Qop_small
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T05:20:59.479094+00:00
-- url     : https://prove2.me/theorems/0736f7dd-f18a-4daa-a91b-5b85cf603c91
-- title:
--   Sobolev: op Bound Qop small
-- statement:
--   The Sobolev construction uses the op Bound Qop small property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/EllipticLocal.lean#L566-L574
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/EllipticLocal.lean#L566-L574

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
variable {m n : ℕ} (a : Fin n → 𝓢(E, ℂ)) (w : Fin n → Fin m → E) (x₀ : E)
variable {cl Cu : ℝ} (hcl : 0 < cl) (hCu : 0 ≤ Cu)
  (hlow : ∀ ξ, cl * ‖ξ‖ ^ m ≤ ‖symb0 (fun i ↦ a i x₀) w ξ‖)
  (hup : ∀ ξ, ‖symb0 (fun i ↦ a i x₀) w ξ‖ ≤ Cu * ‖ξ‖ ^ m)
include hcl hCu hlow hup

theorem GroundTheory.Automorphic.Sobolev.opBound_Qop_small (hm : 1 ≤ m) {μ ε : ℝ} (hμ0 : 0 ≤ μ)
    (hsmall : ∀ ξ : E, ‖qSymb (fun i ↦ a i x₀) w μ ξ‖ * Real.sqrt (1 + ‖ξ‖ ^ 2) ^ (m - 1) ≤ ε)
    (k : ℕ) (s : ℝ) : OpBound (Qop a w x₀ μ k) (s - m + 1) s (k * ε) := by sorry
