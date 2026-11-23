-- Prove2me | Theorems.Thm_GlobalTheory_fourier_extraction_tsum_class
-- name    : GlobalTheory.fourier_extraction_tsum_class
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T12:52:13.128906+00:00
-- url     : https://prove2.me/theorems/df01650b-739d-4a9d-9e0c-5cf02614fa51
-- title:
--   Global Theory: fourier extraction tsum class
-- statement:
--   The Global Theory construction uses the fourier extraction tsum class property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/FourierExtractionTsumClass.lean#L177-L278
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/FourierExtractionTsumClass.lean#L177-L278

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_FourierExtractionTsumClass
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
open Module

theorem GlobalTheory.fourier_extraction_tsum_class :
    ∀ (K X : Type) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (N : ℕ) (ζ : K), 0 < N → ‖(N : K)‖ = 1 → IsPrimitiveRoot ζ N → ∀ (σ : X → K), Filter.Tendsto σ Filter.cofinite (nhds 0) → ∀ α : X, Finite {t : Multiplicative X →* Kˣ // t ^ N = 1} ∧ (∑ᶠ t : {t : Multiplicative X →* Kˣ // t ^ N = 1}, (((t.1 (Multiplicative.ofAdd α))⁻¹ : Kˣ) : K) * ∑' β, σ β * (t.1 (Multiplicative.ofAdd β) : K)) = (N : K) ^ finrank ℤ X * ∑' μ, σ (α + N • μ) ∧ ((∀ μ, μ ≠ 0 → ‖σ (α + N • μ)‖ < ‖σ α‖) → ‖∑' μ, σ (α + N • μ)‖ = ‖σ α‖) := by sorry
