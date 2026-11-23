-- Prove2me | Theorems.Thm_GlobalTheory_OnePoint_exists_point_of_subsingleton_fiber
-- name    : GlobalTheory.OnePoint.exists_point_of_subsingleton_fiber
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T12:05:27.599451+00:00
-- url     : https://prove2.me/theorems/9f28831f-21b1-4be2-bd6b-a130770d39d4
-- title:
--   One Point: exists point of subsingleton fiber
-- statement:
--   The One Point construction uses the exists point of subsingleton fiber property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/IsIntegrallyClosedInFractionFieldPowerSeries.lean#L231-L247
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/IsIntegrallyClosedInFractionFieldPowerSeries.lean#L231-L247

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

theorem GlobalTheory.OnePoint.exists_point_of_subsingleton_fiber [PerfectField K] {X Y T : Scheme.{u}} (κ : X ⟶ Y)
    [LocallyOfFiniteType κ] (y : Spec (.of K) ⟶ Y)
    (Ω : Type u) [Field Ω] [Algebra K Ω] [IsAlgClosed Ω]
    (h : ∀ a b : Spec (.of Ω) ⟶ X, a ≫ κ = specAlg(K, Ω) ≫ y → b ≫ κ = specAlg(K, Ω) ≫ y → a = b)
    [Nonempty T] [IsReduced T] (g : T ⟶ Spec (.of K)) (x : T ⟶ X) (hx : x ≫ κ = g ≫ y) :
    ∃ x₀ : Spec (.of K) ⟶ X, g ≫ x₀ = x ∧ x₀ ≫ κ = y ∧
      ∀ x₁ : Spec (.of K) ⟶ X, g ≫ x₁ = x → x₁ = x₀ := by sorry
