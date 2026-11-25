-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Sobolev_exists_small
-- name    : GroundTheory.Automorphic.Sobolev.exists_small
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T05:19:28.958207+00:00
-- url     : https://prove2.me/theorems/1b4809ad-86c2-5fb3-9baa-c83ae1928dcf
-- title:
--   Sobolev: exists small
-- statement:
--   The Sobolev construction uses the exists small property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/EllipticLocal.lean#L697-L781
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/EllipticLocal.lean#L697-L781

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
variable {m n : ℕ} (a : Fin n → 𝓢(E, ℂ)) (w : Fin n → Fin m → E) (N : 𝓢'(E, ℂ) →L[ℂ] 𝓢'(E, ℂ))
  (x₀ : E) {cl Cu : ℝ} (hcl : 0 < cl) (hCu : 0 ≤ Cu)
  (hlow : ∀ ξ, cl * ‖ξ‖ ^ m ≤ ‖symb0 (fun i ↦ a i x₀) w ξ‖)
  (hup : ∀ ξ, ‖symb0 (fun i ↦ a i x₀) w ξ‖ ≤ Cu * ‖ξ‖ ^ m)
include hcl hCu hlow hup

theorem GroundTheory.Automorphic.Sobolev.exists_small (hm : 1 ≤ m) (hN : HasOrder N ((m : ℝ) - 1)) (k : ℕ) :
    ∃ δ, ∃ hδ : 0 < δ, ∀ S : Finset ℝ, ∃ μ, 0 < μ ∧ μ ≤ 1 ∧ ∀ s ∈ S,
      OpBound (Qop a w x₀ μ k ∘L locM a w N x₀ hδ) s s (1 / 2) ∧
      OpBound (locM a w N x₀ hδ ∘L Qop a w x₀ μ k) s s (1 / 2) := by sorry
