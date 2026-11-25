-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_unitary_adjoin_lattice_image_eq
-- name    : GlobalTheory.T.exists_unitary_adjoin_lattice_image_eq
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T00:39:24.225848+00:00
-- url     : https://prove2.me/theorems/611c0ad8-c6c1-4d7a-9ba2-0d2ec8f6d84e
-- title:
--   T: exists unitary adjoin lattice image eq
-- statement:
--   The T construction uses the exists unitary adjoin lattice image eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsUnitaryAdjoinLatticeImageEqStatement.lean#L8-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsUnitaryAdjoinLatticeImageEqStatement.lean#L8-L17

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsUnitaryAdjoinLatticeImageEq
import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemMatLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsUnitaryAdjoinLatticeImageEqStatement
import Theorems.Thm_GlobalTheory_FormalIsogeny_FiniteReduction_map

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial Matrix GlobalTheory.LatOrb
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.exists_unitary_adjoin_lattice_image_eq : ∀ {O K : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Field K] [Algebra O K] [IsFractionRing O K]
    (n : ℕ) (P₀ : O[X]), IsCoprime P₀ (derivative P₀) →
    ∀ γ : Matrix (Fin n) (Fin n) K, γ.charpoly = P₀.map (algebraMap O K) →
    ∀ σ : K →+* K, (∀ x, σ (σ x) = x) → (∀ a : O, ∃ b : O, σ (algebraMap O K a) = algebraMap O K b) →
    (γ.map σ)ᵀ * γ = 1 →
    ∀ M : Submodule O (Fin n → K), IsLatV O M → (∀ v ∈ M, γ *ᵥ v ∈ M) →
    ∀ p : K[X], IsUnit (aeval γ p) → matLat O (((aeval γ p).map σ)ᵀ * aeval γ p) M = M →
    ∃ t : Matrix (Fin n) (Fin n) K, (t.map σ)ᵀ * t = 1 ∧ t * γ = γ * t ∧ matLat O t M = matLat O (aeval γ p) M := by sorry
