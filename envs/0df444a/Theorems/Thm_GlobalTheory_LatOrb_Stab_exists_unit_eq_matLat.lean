-- Prove2me | Theorems.Thm_GlobalTheory_LatOrb_Stab_exists_unit_eq_matLat
-- name    : GlobalTheory.LatOrb.Stab.exists_unit_eq_matLat
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T00:34:37.029909+00:00
-- url     : https://prove2.me/theorems/8e35afcf-2922-4e9b-80cd-9a6a4b06be87
-- title:
--   Stab: exists unit eq mat Lat
-- statement:
--   The Stab construction uses the exists unit eq mat Lat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsUnitEqOfStableLattices.lean#L41-L158
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsUnitEqOfStableLattices.lean#L41-L158

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemMatLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsCyclicVectorOfSeparableCharpolyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IntegralAevalEqAevalMapOfCoprimeCharpolyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EqMulIntegralClosureOfSeparableInvolutionAlgebra
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EqSubmoduleMulLeftImageIntegralClosureOfSeparabl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsUnitEqOfStableLattices
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
open GlobalTheory GlobalTheory.LatOrb GlobalTheory.LatOrb.Stab

theorem GlobalTheory.LatOrb.Stab.exists_unit_eq_matLat : ∀ {O K : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Field K] [Algebra O K] [IsFractionRing O K]
    (n : ℕ) (P₀ : O[X]), IsCoprime P₀ (derivative P₀) →
    ∀ γ : Matrix (Fin n) (Fin n) K, γ.charpoly = P₀.map (algebraMap O K) →
    ∀ M₁ M₂ : Submodule O (Fin n → K), IsLatV O M₁ → IsLatV O M₂ →
    (∀ v ∈ M₁, γ *ᵥ v ∈ M₁) → (∀ v ∈ M₂, γ *ᵥ v ∈ M₂) →
    ∃ p : K[X], IsUnit (aeval γ p) ∧ M₂ = matLat O (aeval γ p) M₁ := by sorry
