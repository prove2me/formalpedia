-- Prove2me | Theorems.Thm_GlobalTheory_ThetaTranslSpan_mem_of_eigen
-- name    : GlobalTheory.ThetaTranslSpan.mem_of_eigen
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T21:07:25.604837+00:00
-- url     : https://prove2.me/theorems/54268c71-7afb-412d-8faa-321730ca9e26
-- title:
--   Theta Transl Span: mem of eigen
-- statement:
--   The Theta Transl Span construction uses the mem of eigen property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExistsImEqLattice.lean#L13-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExistsImEqLattice.lean#L13-L79

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_FourierCoeffUnitCubeTranslateOfEntirePeriodic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_EntirePeriodicEqZeroOfFourierCoeffEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_CardLePowOfLinearIndependent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_IsUnitOfLagrangian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_CardLePowOfLinearIndependentThetaPrincipal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsImEqLattice
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped ComplexOrder
open GlobalTheory GlobalTheory.ThetaTranslSpan

theorem GlobalTheory.ThetaTranslSpan.mem_of_eigen {V : Type} [AddCommGroup V] (Λ Λ₁ : AddSubgroup V) (hle : Λ₁ ≤ Λ)
    [Finite (Λ ⧸ Λ₁.addSubgroupOf Λ)] (j : V → V → ℂ) (hj0 : ∀ a ∈ Λ, ∀ z, j a z ≠ 0)
    (hj : ∀ a ∈ Λ, ∀ b ∈ Λ, ∀ z, j (a + b) z = j a (z + b) * j b z)
    (D S : Submodule ℂ (V → ℂ)) (F : V → ℂ)
    (hD : ∀ a ∈ Λ, (fun z => (j a z)⁻¹ * F (z + a)) ∈ D)
    (hF : ∀ a ∈ Λ₁, ∀ z, F (z + a) = j a z * F z)
    (hS : ∀ ψ : AddChar Λ ℂ, (∀ a, ‖ψ a‖ = 1) → (∀ a : Λ, (a : V) ∈ Λ₁ → ψ a = 1) → ∀ G ∈ D,
      (∀ (a : Λ) z, G (z + a) = ψ a * j a z * G z) → G ∈ S) : F ∈ S := by sorry
