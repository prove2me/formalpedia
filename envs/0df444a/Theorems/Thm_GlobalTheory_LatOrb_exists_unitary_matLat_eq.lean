-- Prove2me | Theorems.Thm_GlobalTheory_LatOrb_exists_unitary_matLat_eq
-- name    : GlobalTheory.LatOrb.exists_unitary_matLat_eq
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T00:34:02.596809+00:00
-- url     : https://prove2.me/theorems/587aefd6-987d-43b7-ad79-e9408d16c081
-- title:
--   Lat Orb: exists unitary mat Lat eq
-- statement:
--   The Lat Orb construction uses the exists unitary mat Lat eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsUnitaryAdjoinLatticeImageEq.lean#L87-L212
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsUnitaryAdjoinLatticeImageEq.lean#L87-L212

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemMatLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IntegralAevalEqAevalMapOfCoprimeCharpolyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsIntegralMatrixOfMapsToFullRankLatticeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsUnitaryMulIntegralOfNormMaximalOrderUnitStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsUnitaryAdjoinLatticeImageEq
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
noncomputable section
open GlobalTheory GlobalTheory.LatOrb

theorem GlobalTheory.LatOrb.exists_unitary_matLat_eq : ∀ {O K : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Field K] [Algebra O K] [IsFractionRing O K]
    (n : ℕ) (P₀ : O[X]), IsCoprime P₀ (derivative P₀) →
    ∀ γ : Matrix (Fin n) (Fin n) K, γ.charpoly = P₀.map (algebraMap O K) →
    ∀ σ : K →+* K, (∀ x, σ (σ x) = x) → (∀ a : O, ∃ b : O, σ (algebraMap O K a) = algebraMap O K b) →
    (γ.map σ)ᵀ * γ = 1 →
    ∀ M : Submodule O (Fin n → K), IsLatV O M → (∀ v ∈ M, γ *ᵥ v ∈ M) →
    ∀ p : K[X], IsUnit (aeval γ p) → matLat O (((aeval γ p).map σ)ᵀ * aeval γ p) M = M →
    ∃ t : Matrix (Fin n) (Fin n) K, (t.map σ)ᵀ * t = 1 ∧ t * γ = γ * t ∧
      matLat O t M = matLat O (aeval γ p) M := by sorry
