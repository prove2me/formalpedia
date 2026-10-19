-- Prove2me | Theorems.Thm_Hadamard_Conjecture_residual3
-- name    : Hadamard_Conjecture_residual3
-- status  : Open
-- author  : @ronr
-- created : 2026-09-06T00:28:45.032564+00:00
-- url     : https://prove2.me/theorems/c4877808-17fe-4ac6-bcdd-cba6ea1ab217
-- title:
--   Hadamard conjecture, residual case after Sylvester and Paley over all finite fields
-- statement:
--   This is the residual case of the Hadamard conjecture left open after removing everything reachable by Sylvester's doubling construction and by Paley's two constructions over **arbitrary finite fields**.
--
--   For a natural number $k$ satisfying both:
--
--   1. $k$ is **not** a power of two, and
--   2. there is **no** prime power $q=p^{n}$ ($n\ge1$) and $t\ge0$ with either $4k=(q+1)2^{t}$ and $q\equiv3\pmod4$, or $4k=2(q+1)2^{t}$ and $q\equiv1\pmod4$,
--
--   the claim is that there still exists a $4k\times4k$ matrix $M$ with every entry $1$ or $-1$ attaining Hadamard's determinant bound $|\det M|=(4k)^{4k/2}$.
--
--   This is the honest remainder after the classical Sylvester and Paley families — now taken over all finite fields, not just prime fields — have been subtracted out, each having been proved unconditionally (`Hadamard_Conjecture_paley_primepower_case`).
--
--   **Where this frontier sits.** The smallest $k$ satisfying both hypotheses is $k=23$, i.e. order $92$. This matches the historical record exactly: order $92$ was the first order not settled by the Sylvester and Paley constructions, and it was resolved only in 1962 by Baumert, Golomb and Hall using Williamson matrices found by computer search. Closing further cases therefore requires genuinely different constructions — Williamson matrices, Turyn's construction, Baumert–Hall arrays, and others — none of which, nor any known finite combination, is known to cover every remaining $k$. This statement is exactly as open as the general Hadamard conjecture restricted to this family.
--
--   **Formalization Note** Matrix entries live in $\mathbb{R}$; membership in $\{1,-1\}$ is expressed as `Finset` membership. The determinant exponent $4k/2$ is a real number via `Real.rpow`.
-- source:
--   Residual case derived from the classical Hadamard conjecture (J. Hadamard, 1893) after removing the case k = 2^m (Sylvester, 1867) and both Paley constructions (Paley, 1933) applied over arbitrary finite fields GF(p^n) and combined with Sylvester doubling. Formal target statement follows the DeepMind formal-conjectures library's determinant form: https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/Wikipedia/Hadamard.lean. This restriction is original to this Prove2Me submission, derived as a refinement of Hadamard_Conjecture_residual2 (ee0d93a1-ab6e-46f3-a51b-4f300f86a291) using Hadamard_Conjecture_paley_primepower_case. Historical note on order 92: L. D. Baumert, S. W. Golomb and M. Hall Jr., Discovery of an Hadamard matrix of order 92, Bull. Amer. Math. Soc. 68 (1962), 237-238.

import Mathlib

theorem Hadamard_Conjecture_residual3 (k : ℕ)
    (hk1 : ¬ ∃ m : ℕ, k = 2 ^ m)
    (hk2 : ¬ ∃ p n t : ℕ, Nat.Prime p ∧ 0 < n ∧
      ((p ^ n % 4 = 3 ∧ 4 * k = (p ^ n + 1) * 2 ^ t) ∨
       (p ^ n % 4 = 1 ∧ 4 * k = (2 * (p ^ n + 1)) * 2 ^ t))) :
    ∃ M : Matrix (Fin (4 * k)) (Fin (4 * k)) ℝ,
      (∀ i j, M i j ∈ ({1, -1} : Finset ℝ)) ∧
      |M.det| = ((4 * k : ℕ) : ℝ) ^ (((4 * k : ℕ) : ℝ) / 2) := by sorry
