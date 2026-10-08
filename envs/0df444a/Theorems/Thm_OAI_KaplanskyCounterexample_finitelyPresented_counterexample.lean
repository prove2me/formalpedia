-- Prove2me | Theorems.Thm_OAI_KaplanskyCounterexample_finitelyPresented_counterexample
-- name    : OAI.KaplanskyCounterexample.finitelyPresented_counterexample
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-07T04:32:50.866841+00:00
-- url     : https://prove2.me/theorems/34db9af8-ae05-4d0d-b481-af77f482f3d2
-- statement:
--   The theorem states that there exist a finite field K of characteristic 2 and a finitely presented group G such that G contains an element g of odd prime order ℓ (that is, orderOf g = ℓ with ℓ prime and odd), and the group algebra K[G] (the monoid algebra of G over K) contains elements a_out and b_out with a_out · b_out = 1 but b_out · a_out ≠ 1. Thus K[G] fails to be directly finite, giving a counterexample to direct finiteness. The statement is existential: it does not name a specific K, G, or prime ℓ, and the proof is admitted in the source.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/KaplanskyFinitelyPresented.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/KaplanskyFinitelyPresented.lean; bytes 55..585
-- Kind: theorem; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI.KaplanskyCounterexample

/-- A finite characteristic-two field and a finitely presented group with odd-prime
order torsion give a counterexample to direct finiteness (paper, Theorem 1.1). -/
theorem finitelyPresented_counterexample :
    ∃ (K : Type) (_ : Field K) (_ : Fintype K) (_ : CharP K 2),
      ∃ (G : Type) (_ : Group G) (_ : Group.IsFinitelyPresented G),
        (∃ (ℓ : ℕ) (_ : ℓ.Prime) (_ : Odd ℓ) (g : G), orderOf g = ℓ) ∧
        ∃ a_out b_out : MonoidAlgebra K G, a_out * b_out = 1 ∧ b_out * a_out ≠ 1 := by
  sorry

end OAI.KaplanskyCounterexample
