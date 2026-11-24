-- Prove2me | Theorems.Thm_GlobalTheory_HilbFam_exists_summable_bound_terms
-- name    : GlobalTheory.HilbFam.exists_summable_bound_terms
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T14:20:43.409313+00:00
-- url     : https://prove2.me/theorems/fab05b48-09ce-415c-9eac-4705e666dcf1
-- title:
--   Hilb Fam: exists summable bound terms
-- statement:
--   The Hilb Fam construction uses the exists summable bound terms property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsSummableBoundHilbertEisensteinTerms.lean#L25-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsSummableBoundHilbertEisensteinTerms.lean#L25-L75

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasLevelStd
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasQIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SumRealEmbeddingsEqTraceTotallyReal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsSummableBoundHilbertEisensteinTerms
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
open GlobalTheory GlobalTheory.HilbFam

theorem GlobalTheory.HilbFam.exists_summable_bound_terms : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (k : ℕ) (𝔞 𝔟 : Frac F) (a₀ : ℂ) (a : F → ℂ) (x : F) (τ c t : ℂ), IsCoef k 𝔞 𝔟 a₀ a → 0 < τ.im → ∃ M : F → ℝ, Summable M ∧ ∀ (ξ : F) (z : Emb F → ℂ), (∀ i, 1 / 2 ≤ ‖1 + z i * c‖ ∧ τ.im / 2 ≤ (τ + t * z i / (1 + z i * c)).im) → ‖a ξ * eTr (ξ * x) * Complex.exp ((2 * Real.pi * Complex.I) * ((Algebra.trace ℚ F ξ : ℚ) : ℂ) * τ) * ∏ i : Emb F, ((1 + z i * c)⁻¹ ^ k * Complex.exp ((2 * Real.pi * Complex.I) * (i ξ : ℂ) * t * z i / (1 + z i * c)))‖ ≤ M ξ := by sorry
