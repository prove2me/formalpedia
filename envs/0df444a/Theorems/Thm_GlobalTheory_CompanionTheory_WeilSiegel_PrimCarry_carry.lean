-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_WeilSiegel_PrimCarry_carry
-- name    : GlobalTheory.CompanionTheory.WeilSiegel.PrimCarry.carry
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T17:04:23.952053+00:00
-- url     : https://prove2.me/theorems/335254ec-90cc-426e-a9fa-e54a1af1e6ee
-- title:
--   Prim Carry: carry
-- statement:
--   The Prim Carry construction uses the carry property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/HyperbolicPairUnitaryTransitive.lean#L43-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/HyperbolicPairUnitaryTransitive.lean#L43-L51

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
variable {A : Type} [CommRing A] {N : ℕ} {τ : A →+* A} {H : Matrix (Fin N) (Fin N) A}

theorem GlobalTheory.CompanionTheory.WeilSiegel.PrimCarry.carry (hτ : ∀ y, τ (τ y) = y)
    (hcar : ∀ p β : A, IsUnit β → τ β = β → ∃ ε z : A, ε * τ ε = 1 ∧ (β - τ ε * p) * z = 1)
    (hH : ∀ i j, τ (H j i) = H i j) (x y : Fin N → A)
    (hxy : hform τ H x x = hform τ H y y) (hβ : IsUnit (hform τ H x x)) :
    ∃ g ∈ UJ τ H, (g : Matrix (Fin N) (Fin N) A) *ᵥ x = y ∧
      ∀ z, hform τ H x z = 0 → hform τ H y z = 0 → (g : Matrix (Fin N) (Fin N) A) *ᵥ z = z := by sorry
