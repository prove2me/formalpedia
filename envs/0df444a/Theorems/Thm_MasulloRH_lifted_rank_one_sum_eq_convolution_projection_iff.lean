-- Prove2me | Theorems.Thm_MasulloRH_lifted_rank_one_sum_eq_convolution_projection_iff
-- name    : MasulloRH.lifted_rank_one_sum_eq_convolution_projection_iff
-- status  : Proved
-- author  : @Abhishek Anand
-- created : 2026-11-21T04:18:27.835311+00:00
-- url     : https://prove2.me/theorems/dd97b97f-c94c-43f7-a0e2-f75fcf2efe2a
-- title:
--   Identifying the lifted rank-one sum with convolution after projection
-- statement:
--   Suppose the series of lifted rank-one terms has operator-norm sum T. Assume the coefficients are biorthogonal to the lifts, vanish on the kernel of P, and that the lifts together with this kernel span a dense subspace. Then T equals A composed with P exactly when A vⱼ equals A(P vⱼ) for every lift. This isolates the identification required in Masullo’s final sentence on convergence.
-- source:
--   A. M. Masullo, The Music of the Primes, frozen draft, Theorem 10.4.2.8, pp. 463–464, (10.4.2.21)–(10.4.2.25) and the operator identification following (10.4.2.34).

import Mathlib

open InnerProductSpace

theorem MasulloRH.lifted_rank_one_sum_eq_convolution_projection_iff {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (A P T : H →L[ℂ] H) (v η : ℕ → H)
    (hbi : ∀ i j, inner ℂ (η i) (v j) = if i = j then 1 else 0)
    (hk : ∀ i (u : H), P u = 0 → inner ℂ (η i) u = 0)
    (hd : Dense (Submodule.span ℂ (Set.range v ∪ (P.ker : Set H)) : Set H))
    (hT : HasSum (fun i => rankOne ℂ (A (v i)) (η i)) T) :
    T = A.comp P ↔ ∀ j, A (v j) = A (P (v j)) := by sorry
