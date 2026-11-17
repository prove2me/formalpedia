-- Prove2me | Theorems.Thm_N25_hasSum_stabilized_polynomial_product
-- name    : N25.hasSum_stabilized_polynomial_product
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:34:23.657782+00:00
-- url     : https://prove2.me/theorems/b175f5d2-d5bf-48be-9e5a-506a43446091
-- title:
--   A coefficientwise bounded Euler product equals its stabilized series
-- statement:
--   Let $(P_n)_{n≥0}$ be complex polynomials and let $M∈ℂ[X]$. Assume $P_n(0)=M(0)=1$ and $|[X^k]P_n|≤|[X^k]M|$ for every $n,k$. For $q∈ℂ$ with $|q|<1$, put $A_m=[X^m]∏_{0≤n<m}P_n(X^{n+1})$. Then the series with terms $A_mq^m$ sums to the convergent infinite product: $$∑_{m≥0}A_mq^m=∏_{n≥0}P_n(q^{n+1}).$$ This analytic identity turns stabilized formal coefficients into an actual product inside the unit disk.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib

set_option autoImplicit false
open Polynomial
open scoped BigOperators

theorem N25.hasSum_stabilized_polynomial_product
    (P : ℕ → ℂ[X]) (M : ℂ[X])
    (hP : ∀ n, (P n).coeff 0 = 1)
    (hM : M.coeff 0 = 1)
    (hdom : ∀ n k, ‖(P n).coeff k‖ ≤ ‖M.coeff k‖)
    (q : ℂ) (hq : ‖q‖ < 1) :
    HasSum
      (fun m : ℕ =>
        (∏ n ∈ Finset.range m, Polynomial.expand ℂ (n + 1) (P n)).coeff m * q ^ m)
      (∏' n : ℕ, (P n).eval (q ^ (n + 1))) := by sorry
