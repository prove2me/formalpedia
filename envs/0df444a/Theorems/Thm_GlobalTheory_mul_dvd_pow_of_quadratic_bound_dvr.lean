-- Prove2me | Theorems.Thm_GlobalTheory_mul_dvd_pow_of_quadratic_bound_dvr
-- name    : GlobalTheory.mul_dvd_pow_of_quadratic_bound_dvr
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T23:11:47.512711+00:00
-- url     : https://prove2.me/theorems/e03fa454-42ac-41e6-b30b-b39c68f835f5
-- title:
--   Global Theory: mul dvd pow of quadratic bound dvr
-- statement:
--   The Global Theory construction uses the mul dvd pow of quadratic bound dvr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsPowEqMulOfQuadraticBoundNormalLocal.lean#L10-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsPowEqMulOfQuadraticBoundNormalLocal.lean#L10-L45

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ThickTransComp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_RangeAlgebraMapEqIInfDiscreteValuationSubring
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsPowEqMulOfQuadraticBoundNormalLocal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory
open IsDiscreteValuationRing

theorem GlobalTheory.mul_dvd_pow_of_quadratic_bound_dvr {V : Type} [CommRing V] [IsDomain V]
    [IsDiscreteValuationRing V] {X : Type} [AddCommGroup X] (h h' : X →+ X) (C : ℕ)
    (hq : ∀ q : X → ℤ, (∀ y, 0 ≤ q y) → q 0 = 0 → (∀ y, q (-y) = q y) →
      (∀ x y z, q (x + y + z) + q x + q y + q z = q (x + y) + q (x + z) + q (y + z)) →
      (∀ y z, q (h y + z) + q y + q (h' z) = q (y + h' z) + q (h y) + q z) →
      ∀ y, q (h y) ≤ C * q y) {N : ℕ} (hN : C + 1 ≤ N) (k : X → V) (hk0 : ∀ y, k y ≠ 0)
    (h1 : ∀ y, k (-y) = k y) (h2 : k 0 = 1)
    (h3 : ∀ x y z, k (x + y + z) * k x * k y * k z = k (x + y) * k (x + z) * k (y + z))
    (h4 : ∀ y z, ∃ u : V, IsUnit u ∧
      k (h y + z) * k y * k (h' z) = u * (k (y + h' z) * k (h y) * k z)) (y : X) :
    k y * k (h y) ∣ k y ^ N := by sorry
