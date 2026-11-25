-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_unit_eq_of_stable_lattices
-- name    : GlobalTheory.T.exists_unit_eq_of_stable_lattices
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T00:36:03.717041+00:00
-- url     : https://prove2.me/theorems/3ec19b39-04d8-4f0e-9054-eb2c8d3f6866
-- title:
--   T: exists unit eq of stable lattices
-- statement:
--   The T construction uses the exists unit eq of stable lattices property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsUnitEqOfStableLatticesStatement.lean#L8-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsUnitEqOfStableLatticesStatement.lean#L8-L15

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsUnitEqOfStableLattices
import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemMatLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsUnitEqOfStableLatticesStatement
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

theorem GlobalTheory.T.exists_unit_eq_of_stable_lattices : ∀ {O K : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Field K] [Algebra O K] [IsFractionRing O K]
    (n : ℕ) (P₀ : O[X]), IsCoprime P₀ (derivative P₀) →
    ∀ γ : Matrix (Fin n) (Fin n) K, γ.charpoly = P₀.map (algebraMap O K) →
    ∀ M₁ M₂ : Submodule O (Fin n → K), IsLatV O M₁ → IsLatV O M₂ →
    (∀ v ∈ M₁, γ *ᵥ v ∈ M₁) → (∀ v ∈ M₂, γ *ᵥ v ∈ M₂) →
    ∃ p : K[X], IsUnit (aeval γ p) ∧ M₂ = matLat O (aeval γ p) M₁ := by sorry
