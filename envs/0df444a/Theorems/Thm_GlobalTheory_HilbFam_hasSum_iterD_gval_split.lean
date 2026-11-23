-- Prove2me | Theorems.Thm_GlobalTheory_HilbFam_hasSum_iterD_gval_split
-- name    : GlobalTheory.HilbFam.hasSum_iterD_gval_split
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T15:57:30.207357+00:00
-- url     : https://prove2.me/theorems/ff4d5bca-ff57-4795-bb3c-2a78d84d7ee8
-- title:
--   Hilb Fam: has Sum iter D gval split
-- statement:
--   The Hilb Fam construction uses the has Sum iter D gval split property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HasSumIteratedDerivHilbertEisensteinSplitLattice.lean#L18-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HasSumIteratedDerivHilbertEisensteinSplitLattice.lean#L18-L66

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasLevelStd
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasQIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IteratedDerivZeroEqLaguerreDerivativePolynomialVStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IteratedPartialDerivProdOneVarAtZeroStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IteratedPartialDerivConstMulReindexStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasSumIteratedComplexPartialDerivTermwiseStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsSummableBoundHilbertEisensteinTermsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasSumHilbertEisensteinMovedPointStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsRadiusMoebiusPerturbationUpperHalfPlaneStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasSumIteratedDerivHilbertEisensteinSplitLattice
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

theorem GlobalTheory.HilbFam.hasSum_iterD_gval_split : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (k : ℕ) (𝔞 𝔟 : Frac F) (a₀ : ℂ) (a : F → ℂ) (x : F) (τ c t : ℂ) (u : List (Emb F)), Even k → IsCoef k 𝔞 𝔟 a₀ a → 0 < τ.im → HasSum (fun ξ : F ↦ a ξ * eTr (ξ * x) * Complex.exp ((2 * Real.pi * Complex.I) * ((Algebra.trace ℚ F ξ : ℚ) : ℂ) * τ) * ∏ i : Emb F, lag k (u.count i) c ((2 * Real.pi * Complex.I) * (i ξ : ℂ) * t)) (iterD u (fun z ↦ (cK F k : ℂ) * gval k (split 𝔞 𝔟 x) (fun i ↦ τ + z i * (c * τ + t)) (fun i ↦ 1 + z i * c)) 0 / ((2 * Real.pi * Complex.I) ^ Module.finrank ℚ F * (omegaFactor 𝔞 : ℂ)) ^ k) := by sorry
