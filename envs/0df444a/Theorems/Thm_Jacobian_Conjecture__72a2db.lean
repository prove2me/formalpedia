-- Prove2me | Theorems.Thm_Jacobian_Conjecture__72a2db
-- name    : Jacobian_Conjecture
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-06-25T18:45:49.998741+00:00
-- url     : https://prove2.me/theorems/72a2dbd2-3c2b-4de5-ab85-96a668f21f34
-- statement:
--   **Jacobian conjecture.** Over $\mathbb{C}$, any polynomial map $F:\mathbb{C}^n\to\mathbb{C}^n$ whose Jacobian determinant is a nonzero constant (a unit) admits a polynomial inverse $G$, i.e. $G\circ F = F\circ G = \mathrm{id}$. (Polynomial-inverse form, following the DeepMind formal-conjectures library.)
-- source:
--   https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/Wikipedia/JacobianConjecture.lean

import Mathlib

open MvPolynomial

theorem Jacobian_Conjecture {n : ℕ} (F : Fin n → MvPolynomial (Fin n) ℂ)
    (H : IsUnit (Matrix.of (fun i j => pderiv i (F j))).det) :
    ∃ G : Fin n → MvPolynomial (Fin n) ℂ,
      (∀ i, bind₁ G (F i) = X i) ∧ (∀ i, bind₁ F (G i) = X i) := by sorry
