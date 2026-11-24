-- Prove2me | Theorems.Thm_GlobalTheory_HilbFam_hser_coeff_isAlgebraic
-- name    : GlobalTheory.HilbFam.hser_coeff_isAlgebraic
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T14:20:48.353798+00:00
-- url     : https://prove2.me/theorems/f3940b00-a945-4353-871e-99252f5f923f
-- title:
--   Hilb Fam: hser coeff is Algebraic
-- statement:
--   The Hilb Fam construction uses the hser coeff is Algebraic property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HilbertDiagonalRestrictionCoeffIsAlgebraic.lean#L84-L97
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HilbertDiagonalRestrictionCoeffIsAlgebraic.lean#L84-L97

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasLevelStd
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasQIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_OmegaFactorPowTwoMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HilbertDiagonalRestrictionCoeffIsAlgebraic
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

theorem GlobalTheory.HilbFam.hser_coeff_isAlgebraic : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (k : ℕ) (𝔞 𝔟 : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Frac F) (a₀ : ℂ) (a : F → ℂ) (x : F) (s N : ℕ) (κ : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F → ℕ) (c : ℕ → ℂ) (n : ℕ), k = 2 * s → _root_.GlobalTheory.HilbFam.IsCoef k 𝔞 𝔟 a₀ a → IsAlgebraic ℚ a₀ → (∀ m, IsAlgebraic ℚ (c m)) → IsAlgebraic ℚ (PowerSeries.coeff n (_root_.GlobalTheory.HilbFam.hser k N 𝔞 a x κ c)) := by sorry
