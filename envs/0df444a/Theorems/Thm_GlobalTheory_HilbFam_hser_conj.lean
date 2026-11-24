-- Prove2me | Theorems.Thm_GlobalTheory_HilbFam_hser_conj
-- name    : GlobalTheory.HilbFam.hser_conj
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T14:21:12.889802+00:00
-- url     : https://prove2.me/theorems/5d602355-2597-48c8-af0e-bbb4ede26b33
-- title:
--   Hilb Fam: hser conj
-- statement:
--   The Hilb Fam construction uses the hser conj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HilbertEisensteinSeriesRingEquivConj.lean#L22-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HilbertEisensteinSeriesRingEquivConj.lean#L22-L61

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasLevelStd
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasQIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HilbertEisensteinFourierCoeffRingEquivConj
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_OmegaFactorPowTwoMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HilbertEisensteinSeriesRingEquivConj
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

theorem GlobalTheory.HilbFam.hser_conj : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (k : ℕ) (𝔞 𝔟 : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Frac F) (a₀ : ℂ) (a : F → ℂ) (x : F) (s N : ℕ) (g : ℂ ≃+* ℂ) (m : ℤ) (π : Equiv.Perm (_root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F)) (κ : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F → ℕ) (c : ℕ → ℂ) (n : ℕ), k = 2 * s → 0 < N → _root_.GlobalTheory.HilbFam.IsCoef k 𝔞 𝔟 a₀ a → g a₀ = a₀ → _root_.GlobalTheory.HilbFam.HasLevel N (_root_.GlobalTheory.HilbFam.split 𝔞 𝔟 x) → g (Complex.exp ((2 * Real.pi * Complex.I) / N)) = Complex.exp ((2 * Real.pi * Complex.I) * m / N) → (∀ (i : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F) (y : F), g ((i y : ℝ) : ℂ) = ((π i y : ℝ) : ℂ)) → g (PowerSeries.coeff n (_root_.GlobalTheory.HilbFam.hser k N 𝔞 a x κ c)) = PowerSeries.coeff n (_root_.GlobalTheory.HilbFam.hser k N 𝔞 a (m * x) (fun j ↦ κ (π.symm j)) (fun n ↦ g (c n))) := by sorry
