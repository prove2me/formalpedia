-- Prove2me | Theorems.Thm_GlobalTheory_HilbFam_coef_support_trace
-- name    : GlobalTheory.HilbFam.coef_support_trace
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T14:20:51.315671+00:00
-- url     : https://prove2.me/theorems/80d4eb9d-29cd-4521-b60d-d9dd2c7206e4
-- title:
--   Hilb Fam: coef support trace
-- statement:
--   The Hilb Fam construction uses the coef support trace property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HilbertEisensteinCoeffSupportTraceFinite.lean#L161-L167
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HilbertEisensteinCoeffSupportTraceFinite.lean#L161-L167

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasLevelStd
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasQIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SplitLatticeLevelTraceDenominatorStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SumRealEmbeddingsEqTraceTotallyRealStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HilbertEisensteinCoeffSupportTraceFinite
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
open NumberField UpperHalfPlane
open scoped Classical MatrixGroups nonZeroDivisors

theorem GlobalTheory.HilbFam.coef_support_trace : ∀ (F : Type) [Field F] [NumberField F]
    [IsTotallyReal F] (k : ℕ) (𝔞 𝔟 : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Frac F) (a₀ : ℂ) (a : F → ℂ) (x : F)
    (N : ℕ), 0 < N → _root_.GlobalTheory.HilbFam.IsCoef k 𝔞 𝔟 a₀ a →
    _root_.GlobalTheory.HilbFam.HasLevel N (_root_.GlobalTheory.HilbFam.split 𝔞 𝔟 x) →
    (∀ ξ, a ξ ≠ 0 → ∃ n : ℕ, (N : ℚ) * Algebra.trace ℚ F ξ = n) ∧
      ∀ n : ℕ, {ξ : F | a ξ ≠ 0 ∧ (N : ℚ) * Algebra.trace ℚ F ξ = n}.Finite := by sorry
