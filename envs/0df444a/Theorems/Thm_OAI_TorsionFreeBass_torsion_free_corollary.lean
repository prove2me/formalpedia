-- Prove2me | Theorems.Thm_OAI_TorsionFreeBass_torsion_free_corollary
-- name    : OAI.TorsionFreeBass.torsion_free_corollary
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-07T04:33:32.566324+00:00
-- url     : https://prove2.me/theorems/22e79a4b-c4ca-4cbe-81df-3e42aa55651f
-- statement:
--   The theorem states that, for a group G that is torsion-free in the usual sense (the identity is its only element of finite order), two things hold. First, for every size q ≥ 1 and every q×q matrix e over the complex group algebra ℂ[G] with e² = e, the matrix trace of e (the sum of the identity-coefficients of its diagonal entries) equals the rank over ℂ of the entrywise augmentation of e (each entry replaced by the sum of its coefficients), viewed as a complex number. Also, the identity-coefficient trace traceK0 on algebraic K₀ of ℂ[G], presented by idempotent matrices modulo isomorphism and direct-sum relations, equals the augmentation rank map to ℤ followed by the inclusion ℤ → ℂ, and the range of traceK0 is exactly the set of integers inside ℂ. Second, for every commutative integral domain R of characteristic zero, every idempotent e in the group ring R[G] satisfies e = 0 or e = 1. The theorem is stated with its proof admitted.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/BassTorsionFree.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/BassTorsionFree.lean; bytes 11850..12506
-- Kind: theorem; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib
import Definitions.Def_BassTorsionFree

namespace OAI

open Set MeasureTheory

open Finset MeasureTheory intervalIntegral

open scoped Classical BigOperators

noncomputable section

namespace TorsionFreeBass

variable {G : Type*} [Group G]

/-- Trace/rank, equality and range on algebraic K₀, and characteristic-zero
scalar idempotents for torsion-free groups. -/
theorem torsion_free_corollary (G : Type*) [Group G] (hG : TorsionFree G) :
    ((∀ (q : ℕ), 1 ≤ q →
      ∀ e : Matrix (Fin q) (Fin q) (MonoidAlgebra ℂ G), e ^ 2 = e →
        matrixTrace e = ((augmentedMatrix e).rank : ℂ)) ∧
      traceK0 (G := G) = (Int.castAddHom ℂ).comp augmentationRank ∧
      Set.range (traceK0 (G := G)) = Set.range (fun z : ℤ => (z : ℂ))) ∧
    (∀ (R : Type*) [CommRing R] [IsDomain R] [CharZero R]
      (e : MonoidAlgebra R G), e ^ 2 = e → e = 0 ∨ e = 1) := by
  sorry

end TorsionFreeBass
end
end OAI
