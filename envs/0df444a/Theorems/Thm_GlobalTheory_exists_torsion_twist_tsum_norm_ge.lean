-- Prove2me | Theorems.Thm_GlobalTheory_exists_torsion_twist_tsum_norm_ge
-- name    : GlobalTheory.exists_torsion_twist_tsum_norm_ge
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T22:41:53.734111+00:00
-- url     : https://prove2.me/theorems/c65b0a10-777b-4262-9f5b-4a214f091771
-- title:
--   Global Theory: exists torsion twist tsum norm ge
-- statement:
--   The Global Theory construction uses the exists torsion twist tsum norm ge property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsTorsionTwistTsumNormGe.lean#L8-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsTorsionTwistTsumNormGe.lean#L8-L38

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_FourierExtractionTsumClass
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsTorsionTwistTsumNormGe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module
open GlobalTheory

theorem GlobalTheory.exists_torsion_twist_tsum_norm_ge :
    ∀ (K X : Type) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (N : ℕ) (ζ : K), 0 < N → ‖(N : K)‖ = 1 → IsPrimitiveRoot ζ N → ∀ (σ : X → K) (q : X → ℝ) (r : ℝ), 0 < r → r < 1 → Filter.Tendsto q Filter.cofinite Filter.atTop → (∀ z, ‖σ z‖ ≤ r ^ q z) → ∀ z₀ : X, ‖σ z₀‖ = r ^ q z₀ → (∀ μ, μ ≠ 0 → q z₀ < q (z₀ + N • μ)) → ∃ t : Multiplicative X →* Kˣ, t ^ N = 1 ∧ r ^ q z₀ ≤ ‖∑' z, σ z * (t (Multiplicative.ofAdd z) : K)‖ := by sorry
