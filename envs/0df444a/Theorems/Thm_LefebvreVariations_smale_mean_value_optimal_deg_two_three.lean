-- Prove2me | Theorems.Thm_LefebvreVariations_smale_mean_value_optimal_deg_two_three
-- name    : LefebvreVariations.smale_mean_value_optimal_deg_two_three
-- status  : Proved
-- author  : @Secousses
-- created : 2026-11-24T22:03:00.111813+00:00
-- url     : https://prove2.me/theorems/2527aa36-6a89-4eb4-b1d9-691f3f5a313d
-- title:
--   Lefebvre's variations, No. 7 — on a theme by Smale: Smale's mean value conjecture with optimal constant in degrees 2 and 3
-- statement:
--   This is Smale's mean value conjecture with the optimal constant, in degrees $2$ and $3$.
--
--   Let $P\in\mathbb C[X]$ have degree $d\in\{2,3\}$ and let $z\in\mathbb C$ be a point that is not a critical point, $P'(z)\neq0$. Then there is a critical point $c$ of $P$, that is $P'(c)=0$, such that
--
--   $$
--   \left|\frac{P(z)-P(c)}{z-c}\right|\ \le\ \frac{d-1}{d}\,\big|P'(z)\big| .
--   $$
--
--   Smale (1981) proved such a bound with the constant $4$ in place of $\frac{d-1}{d}$ and conjectured that the constant $1$ works; the sharp form asks for $\frac{d-1}{d}$, which is attained by $P(X)=X^d-dX$ at $z=0$. In degree $2$ the bound holds with equality. In degree $3$, writing $P'=3a(X-c_1)(X-c_2)$, the points $z$ where the bound fails at $c_1$ and those where it fails at $c_2$ form two disjoint open discs, so one of the two critical points always works.
--
--   **Formalization Note** The polynomial is any $P$ with $2\le\deg P\le3$ (no normalization), and the critical point $c$ is chosen depending on $z$; $c\neq z$ follows from $P'(c)=0\neq P'(z)$.
--
--   **Why this is a variation.** This varies Smale's mean value conjecture (`SmaleMeanValue.smale_mean_value_conjecture` and its sharp form with constant $(d-1)/d$, `SmaleMeanValue.smale_mean_value_conjecture_optimal`). It is the special case of the sharp constant for polynomials of degree $2$ and $3$, the lowest degrees, where the bound is elementary. Settling it checks the sharp constant in the first cases beyond which the parent is open, and the extremal polynomial $X^d-dX$ shows the constant cannot be improved.
--
--   **Attribution.** This statement belongs to *Lefebvre's variations*, a series proposed by Erwan Lefebvre: each variation plays an open problem of the platform at its first non-trivial size, so that it can be settled and then reused to attack the open problem itself.
-- source:
--   S. Smale, The fundamental theorem of algebra and complexity theory, Bull. Amer. Math. Soc. (N.S.) 4 (1981), no. 1, 1–36 (mean value theorem with constant 4, conjecture with constant 1, optimal constant (d−1)/d). The low-degree cases of the sharp form are classical: D. Tischler, Critical points and values of complex polynomials, J. Complexity 5 (1989), 438–456. Parent problems: SmaleMeanValue.smale_mean_value_conjecture and SmaleMeanValue.smale_mean_value_conjecture_optimal.

import Mathlib

set_option autoImplicit false

open Polynomial

namespace LefebvreVariations

/-- Smale's mean value conjecture with the optimal constant `(d-1)/d`, in degrees `2` and `3`
(the elementary cases of Smale 1981; the cubic case reduces to the disjointness of two discs). -/
theorem smale_mean_value_optimal_deg_two_three (P : ℂ[X]) (hP2 : 2 ≤ P.natDegree)
    (hP3 : P.natDegree ≤ 3) (z : ℂ) (hz : P.derivative.eval z ≠ 0) :
    ∃ c : ℂ, P.derivative.eval c = 0 ∧
      ‖(P.eval z - P.eval c) / (z - c)‖ ≤
        (((P.natDegree : ℝ) - 1) / P.natDegree) * ‖P.derivative.eval z‖ := by
  sorry

end LefebvreVariations
