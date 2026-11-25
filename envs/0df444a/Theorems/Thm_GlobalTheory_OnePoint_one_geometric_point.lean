-- Prove2me | Theorems.Thm_GlobalTheory_OnePoint_one_geometric_point
-- name    : GlobalTheory.OnePoint.one_geometric_point
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T12:14:59.236363+00:00
-- url     : https://prove2.me/theorems/69a5671b-dee0-4489-b2c6-69494d605514
-- title:
--   One Point: one geometric point
-- statement:
--   The One Point construction uses the one geometric point property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/IsIntegrallyClosedInFractionFieldPowerSeries.lean#L334-L354
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/IsIntegrallyClosedInFractionFieldPowerSeries.lean#L334-L354

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

theorem GlobalTheory.OnePoint.one_geometric_point (K : Type u) [Field K] [PerfectField K] :
    (∀ (F : Scheme.{u}) [Nonempty F] (f : F ⟶ Spec (.of K)) [LocallyOfFiniteType f]
      (Ω : Type u) [Field Ω] [Algebra K Ω] [IsAlgClosed Ω],
      (∀ a b : Spec (.of Ω) ⟶ F, a ≫ f = specAlg(K, Ω) → b ≫ f = specAlg(K, Ω) → a = b) →
      IsIso (F.nilradical.subschemeι ≫ f)) ∧
    (∀ (X Y : Scheme.{u}) (κ : X ⟶ Y) [LocallyOfFiniteType κ],
      (∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω],
        Function.Injective fun a : Spec (.of Ω) ⟶ X ↦ a ≫ κ) →
      ∀ (K' : Type u) [Field K'] [Algebra K K'] (x : Spec (.of K') ⟶ X) (y : Spec (.of K) ⟶ Y),
        x ≫ κ = specAlg(K, K') ≫ y →
        ∃ x₀ : Spec (.of K) ⟶ X, specAlg(K, K') ≫ x₀ = x ∧ x₀ ≫ κ = y) ∧
    (∀ x : K⸨X⸩, IsAlgebraic K x → ∃ c : K, x = HahnSeries.C c) ∧
    (∀ (F : Scheme.{u}) (f : F ⟶ Spec (.of K)) [LocallyQuasiFinite f]
      (x : Spec (.of K⸨X⸩) ⟶ F), x ≫ f = specAlg(K, K⸨X⸩) →
      ∃ x₀ : Spec (.of K) ⟶ F, specAlg(K, K⸨X⸩) ≫ x₀ = x ∧ x₀ ≫ f = 𝟙 _) := by sorry
