-- Prove2me | Theorems.Thm_GlobalTheory_exists_padic_point_scheme
-- name    : GlobalTheory.exists_padic_point_scheme
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T13:50:21.847014+00:00
-- url     : https://prove2.me/theorems/8b3ee317-4f7e-545e-91a9-93df68166f3d
-- title:
--   Global Theory: exists padic point scheme
-- statement:
--   The Global Theory construction uses the exists padic point scheme property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/IsDiscreteValuationRingIntegralClosurePadicInt.lean#L483-L491
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/IsDiscreteValuationRingIntegralClosurePadicInt.lean#L483-L491

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

theorem GlobalTheory.exists_padic_point_scheme {Z : Scheme.{0}} [IsIntegral Z]
    (π : Z ⟶ Spec (.of ℤ)) [Flat π] [LocallyOfFiniteType π] {z : Z} (hz : IsClosed ({z} : Set Z))
    (hp : (p : Z.residueField z) = 0) (U : Z.Opens) (hU : (U : Set Z).Nonempty) :
    ∃ (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (_ : FiniteDimensional ℚ_[p] K)
      (y : Spec (.of (integralClosure ℤ_[p] K)) ⟶ Z),
        y (closedPoint (integralClosure ℤ_[p] K)) = z ∧ y (genericPoint _) ∈ U ∧
          π (y (genericPoint _)) = genericPoint _ := by sorry
