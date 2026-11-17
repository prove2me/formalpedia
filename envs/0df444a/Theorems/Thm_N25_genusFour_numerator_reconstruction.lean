-- Prove2me | Theorems.Thm_N25_genusFour_numerator_reconstruction
-- name    : N25.genusFour_numerator_reconstruction
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:44:56.678527+00:00
-- url     : https://prove2.me/theorems/05c528ad-ebc9-4ade-8043-6f8b497d88ec
-- title:
--   Reconstruction of a genus-four reciprocal numerator
-- statement:
--   Let $L(T)=\sum_jc_jT^j\in\mathbf Z[T]$ have degree at most $8$ and $c_0=1$, and let $q\ne0$. For integers $N_1,\ldots,N_4$, set $s_n=q^n+1-N_n$. Assume $(c_1,c_2,c_3,c_4)$ and $(a_1,a_2,a_3,a_4)$ both satisfy the first four Newton equations for $s_1,\ldots,s_4$, and assume $c_{8-i}q^i=q^4c_i$ for $0\le i\le8$. Then
--
--   $$L(T)=1+a_1T+a_2T^2+a_3T^3+a_4T^4+qa_3T^5+q^2a_2T^6+q^3a_1T^7+q^4T^8.$$
--
--   This is the abstract reconstruction step for the two candidate genus-four numerators.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Definitions.Def_N25_GenusFourNumerator

open N25

theorem N25.genusFour_numerator_reconstruction
    (L : Polynomial ℤ) (q a₁ a₂ a₃ a₄ N₁ N₂ N₃ N₄ : ℤ)
    (hq : q ≠ 0) (hdegree : L.natDegree ≤ 8) (hzero : L.coeff 0 = 1)
    (hnewton : CountNewtonFourEquations q N₁ N₂ N₃ N₄
      (L.coeff 1) (L.coeff 2) (L.coeff 3) (L.coeff 4))
    (hcandidate : CountNewtonFourEquations q N₁ N₂ N₃ N₄ a₁ a₂ a₃ a₄)
    (hrec : ∀ i ≤ 8, L.coeff (8 - i) * q ^ i = q ^ 4 * L.coeff i) :
    L = genusFourNumerator q a₁ a₂ a₃ a₄ := by sorry
