-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_WeilSiegel_PrimCarry_exists_unitary_carry_primitive
-- name    : GlobalTheory.CompanionTheory.WeilSiegel.PrimCarry.exists_unitary_carry_primitive
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T17:04:47.340618+00:00
-- url     : https://prove2.me/theorems/99e326e2-58e4-4a1a-aba6-6107b095b931
-- title:
--   Prim Carry: exists unitary carry primitive
-- statement:
--   The Prim Carry construction uses the exists unitary carry primitive property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/HyperbolicPairUnitaryTransitive.lean#L87-L139
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/HyperbolicPairUnitaryTransitive.lean#L87-L139

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_LatticeGramScalarAlmostAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_HyperbolicPairUnitaryTransitive
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open HeckeCharacterZeroLocus.SiegelWeilU
open scoped Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.WeilSiegel GlobalTheory.CompanionTheory.WeilSiegel.PrimCarry
open GlobalTheory.CompanionTheory.SW.QuasiRefl

theorem GlobalTheory.CompanionTheory.WeilSiegel.PrimCarry.exists_unitary_carry_primitive :
    ∀ (A : Type) [CommRing A] (τ : A →+* A), (∀ y, τ (τ y) = y) → IsUnit (2 : A) →
    (∀ p β : A, IsUnit β → τ β = β → ∃ ε z : A, ε * τ ε = 1 ∧ (β - τ ε * p) * z = 1) →
    ∀ (N : ℕ) (H Hi : Matrix (Fin N) (Fin N) A), H * Hi = 1 → (∀ i j, τ (H j i) = H i j) →
    ∀ e f y a : Fin N → A, hform τ H e e = 0 → hform τ H f f = 0 → hform τ H e f = 1 →
    hform τ H y y = 0 → ∑ k, a k * y k = 1 →
    ∃ g ∈ UJ τ H, (g : Matrix (Fin N) (Fin N) A) *ᵥ e = y := by sorry
