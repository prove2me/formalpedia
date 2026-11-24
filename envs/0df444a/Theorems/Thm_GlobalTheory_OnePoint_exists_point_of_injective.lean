-- Prove2me | Theorems.Thm_GlobalTheory_OnePoint_exists_point_of_injective
-- name    : GlobalTheory.OnePoint.exists_point_of_injective
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T18:38:02.092874+00:00
-- url     : https://prove2.me/theorems/88d65af7-b1ab-466f-9c2c-1788675291da
-- title:
--   One Point: exists point of injective
-- statement:
--   The One Point construction uses the exists point of injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/IsIntegrallyClosedInFractionFieldPowerSeries.lean#L249-L258
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/IsIntegrallyClosedInFractionFieldPowerSeries.lean#L249-L258

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsIntegrallyClosedInFractionFieldPowerSeries
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped LaurentSeries PowerSeries
open CategoryTheory Limits AlgebraicGeometry
open GlobalTheory GlobalTheory.OnePoint
universe u v w
local notation "specAlg(" K ", " L ")" => Spec.map (CommRingCat.ofHom (algebraMap K L))
variable {K : Type u} [Field K]

theorem GlobalTheory.OnePoint.exists_point_of_injective [PerfectField K] {X Y : Scheme.{u}} (κ : X ⟶ Y)
    [LocallyOfFiniteType κ]
    (h : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω],
      Function.Injective fun a : Spec (.of Ω) ⟶ X ↦ a ≫ κ)
    (K' : Type u) [Field K'] [Algebra K K'] (x : Spec (.of K') ⟶ X) (y : Spec (.of K) ⟶ Y)
    (hx : x ≫ κ = specAlg(K, K') ≫ y) :
    ∃ x₀ : Spec (.of K) ⟶ X, specAlg(K, K') ≫ x₀ = x ∧ x₀ ≫ κ = y ∧
      ∀ x₁ : Spec (.of K) ⟶ X, specAlg(K, K') ≫ x₁ = x → x₁ = x₀ := by sorry
