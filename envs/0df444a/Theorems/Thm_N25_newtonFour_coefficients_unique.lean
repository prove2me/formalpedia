-- Prove2me | Theorems.Thm_N25_newtonFour_coefficients_unique
-- name    : N25.newtonFour_coefficients_unique
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:44:56.164794+00:00
-- url     : https://prove2.me/theorems/78271043-1036-4551-bb69-51cd6210af49
-- title:
--   Uniqueness in the first four Newton identities
-- statement:
--   Let $s_1,s_2,s_3,s_4\in\mathbf Z$. Suppose two integer quadruples $(a_1,a_2,a_3,a_4)$ and $(b_1,b_2,b_3,b_4)$ each satisfy the first four Newton equations with these power sums: $c_1+s_1=0$, $2c_2+s_1c_1+s_2=0$, $3c_3+s_1c_2+s_2c_1+s_3=0$, and $4c_4+s_1c_3+s_2c_2+s_3c_1+s_4=0$. Then
--
--   $$(a_1,a_2,a_3,a_4)=(b_1,b_2,b_3,b_4).$$
--
--   This makes the first half of a genus-four reciprocal numerator uniquely recoverable from four point counts.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Definitions.Def_N25_GenusFourNumerator

open N25

theorem N25.newtonFour_coefficients_unique
    {s₁ s₂ s₃ s₄ a₁ a₂ a₃ a₄ b₁ b₂ b₃ b₄ : ℤ}
    (ha : NewtonFourEquations s₁ s₂ s₃ s₄ a₁ a₂ a₃ a₄)
    (hb : NewtonFourEquations s₁ s₂ s₃ s₄ b₁ b₂ b₃ b₄) :
    a₁ = b₁ ∧ a₂ = b₂ ∧ a₃ = b₃ ∧ a₄ = b₄ := by sorry
