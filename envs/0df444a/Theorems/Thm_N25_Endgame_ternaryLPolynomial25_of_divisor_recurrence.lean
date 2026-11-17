-- Prove2me | Theorems.Thm_N25_Endgame_ternaryLPolynomial25_of_divisor_recurrence
-- name    : N25.Endgame.ternaryLPolynomial25_of_divisor_recurrence
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:44:55.191397+00:00
-- url     : https://prove2.me/theorems/a7dacdbd-e608-4758-aa96-9f02b2b2f360
-- title:
--   The divisor recurrences determine the ternary genus-four numerator
-- statement:
--   Let $L∈ℤ[T]$, $A:ℕ→ℤ$, and $N_1,…,N_4∈ℤ$. Assume $deg L≤8$, $L(0)=1$, $(N_1,N_2,N_3,N_4)=(5,5,20,89)$, the stated recurrences for $A_0,…,A_4$, the four stated low-coefficient formulas, and $[T^{8-i}]L·3^i=3^4[T^i]L$ for $0≤i≤8$. Then $$L=1+T-2T^2-5T^3+T^4-15T^5-18T^6+27T^7+81T^8.$$ This identifies the characteristic-three zeta numerator.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Definitions.Def_N25_GenusFourNumerator

set_option autoImplicit false
open N25
open N25.Endgame

theorem N25.Endgame.ternaryLPolynomial25_of_divisor_recurrence
    (L : Polynomial ℤ) (A : ℕ → ℤ) (N₁ N₂ N₃ N₄ : ℤ)
    (hN₁ : N₁ = 5) (hN₂ : N₂ = 5) (hN₃ : N₃ = 20) (hN₄ : N₄ = 89)
    (hdegree : L.natDegree ≤ 8) (hzero : L.coeff 0 = 1)
    (hrec : ∀ i ≤ 8, L.coeff (8 - i) * 3 ^ i = 3 ^ 4 * L.coeff i)
    (hA₀ : A 0 = 1)
    (hA₁ : A 1 = N₁ * A 0)
    (hA₂ : 2 * A 2 = N₁ * A 1 + N₂ * A 0)
    (hA₃ : 3 * A 3 = N₁ * A 2 + N₂ * A 1 + N₃ * A 0)
    (hA₄ : 4 * A 4 = N₁ * A 3 + N₂ * A 2 + N₃ * A 1 + N₄ * A 0)
    (hc₁ : L.coeff 1 = A 1 - 4 * A 0)
    (hc₂ : L.coeff 2 = A 2 - 4 * A 1 + 3 * A 0)
    (hc₃ : L.coeff 3 = A 3 - 4 * A 2 + 3 * A 1)
    (hc₄ : L.coeff 4 = A 4 - 4 * A 3 + 3 * A 2) :
    L = ternaryLPolynomial25 := by sorry
