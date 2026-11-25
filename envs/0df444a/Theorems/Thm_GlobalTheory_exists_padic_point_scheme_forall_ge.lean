-- Prove2me | Theorems.Thm_GlobalTheory_exists_padic_point_scheme_forall_ge
-- name    : GlobalTheory.exists_padic_point_scheme_forall_ge
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T13:51:16.776101+00:00
-- url     : https://prove2.me/theorems/6c72c15d-4be1-4de6-bd28-f53cf3f04cee
-- title:
--   Global Theory: exists padic point scheme forall ge
-- statement:
--   The Global Theory construction uses the exists padic point scheme forall ge property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/IsDiscreteValuationRingIntegralClosurePadicInt.lean#L449-L481
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/IsDiscreteValuationRingIntegralClosurePadicInt.lean#L449-L481

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PrimeEqBotOrMaximalIdealOfIsFieldAway
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_FiniteAlgebraLocalCompletion
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_IntToRatA
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsDiscreteValuationRingIntegralClosurePadicInt
import Theorems.Thm_P2M_UpperTheory_Reformulated_B_Qk17_isPrecomplete_finite_module__f12f74bf6019

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open IsLocalRing TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
variable {p : ℕ} [Fact p.Prime]

theorem GlobalTheory.exists_padic_point_scheme_forall_ge {Z : Scheme.{0}} [IsIntegral Z]
    (π : Z ⟶ Spec (.of ℤ)) [Flat π] [LocallyOfFiniteType π] {z : Z} (hz : IsClosed ({z} : Set Z))
    (hp : (p : Z.residueField z) = 0) (U : Z.Opens) (hU : (U : Set Z).Nonempty) :
    ∃ K₀ : IntermediateField ℚ_[p] (PadicAlgCl p), FiniteDimensional ℚ_[p] K₀ ∧
      ∀ (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K], K₀ ≤ K →
        ∃ y : Spec (.of (integralClosure ℤ_[p] K)) ⟶ Z,
          y (closedPoint (integralClosure ℤ_[p] K)) = z ∧ y (genericPoint _) ∈ U ∧
            π (y (genericPoint _)) = genericPoint _ := by sorry
