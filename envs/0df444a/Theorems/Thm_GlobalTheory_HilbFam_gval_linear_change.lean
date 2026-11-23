-- Prove2me | Theorems.Thm_GlobalTheory_HilbFam_gval_linear_change
-- name    : GlobalTheory.HilbFam.gval_linear_change
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T15:35:09.184493+00:00
-- url     : https://prove2.me/theorems/0675aec7-ea03-4fab-848d-e3a0f63af339
-- title:
--   Hilb Fam: gval linear change
-- statement:
--   The Hilb Fam construction uses the gval linear change property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HilbertEisensteinValueLinearChange.lean#L113-L129
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HilbertEisensteinValueLinearChange.lean#L113-L129

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasLevelStd
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasQIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HilbertEisensteinValueLinearTransfer
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HilbertEisensteinLatticeValueEqOfIsValueStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HilbertEisensteinValueLinearChange
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
set_option autoImplicit false
open NumberField UpperHalfPlane
open scoped Classical MatrixGroups nonZeroDivisors

theorem GlobalTheory.HilbFam.gval_linear_change : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (k : ℕ) (L L' : _root_.GlobalTheory.HilbFam.Lat F) (T : (Fin 2 → F) ≃ₗ[F] (Fin 2 → F)) (b a b' a' lam : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F → ℂ), Even k → (∀ x, x ∈ L ↔ T x ∈ L') → (∀ i, lam i ≠ 0) → (∀ x i, _root_.GlobalTheory.HilbFam.coord b a x i = lam i * _root_.GlobalTheory.HilbFam.coord b' a' (T x) i) → _root_.GlobalTheory.HilbFam.gval k L b a = (∏ i, lam i)⁻¹ ^ k * _root_.GlobalTheory.HilbFam.gval k L' b' a' := by sorry
