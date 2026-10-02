-- Prove2me | Theorems.Thm_LeblSCV_Pseudoconvex_rado
-- name    : LeblSCV.Pseudoconvex.rado
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T06:05:34.971404+00:00
-- url     : https://prove2.me/theorems/b828bdea-3695-4181-8962-2012ff031582
-- title:
--   Theorem 2.4.12 (Radó) — continuous functions holomorphic off their zero set
-- statement:
--   Let $U \subset \mathbb{C}^n$ be open and $f : U \to \mathbb{C}$ a continuous function that is holomorphic on the set
--   $$U' = \{ z \in U : f(z) \neq 0 \}.$$
--   Then $f \in \mathcal{O}(U)$.
--
--   Unlike the Riemann extension theorem, nothing is assumed about the zero set of $f$; continuity and vanishing on it suffice.
--
--   **Formalization Note.** **Formalization Note.** $\mathbb{C}^n$ is `EuclideanSpace ℂ (Fin n)`, so its norm, balls and distances are Euclidean, as in the book. Holomorphic on an open set is `DifferentiableOn ℂ`, which is equivalent to the book's Definition 1.1.2 on open sets (Proposition 1.1.3 and Theorem 1.2.1).
-- source:
--   Lebl, Tasty Bits of Several Complex Variables, version 4.4 (2026), p. 88, Theorem 2.4.12

import Mathlib

namespace LeblSCV.Pseudoconvex

/-- Theorem 2.4.12 (Radó; Lebl, p. 88). Let `U ⊂ ℂⁿ` be open and `f : U → ℂ` a continuous
function that is holomorphic on `U' = {z ∈ U : f(z) ≠ 0}`. Then `f ∈ 𝒪(U)`. Holomorphic on an
open set is `DifferentiableOn ℂ`. -/
theorem rado {n : ℕ} (U : Set (EuclideanSpace ℂ (Fin n))) (hU : IsOpen U)
    (f : EuclideanSpace ℂ (Fin n) → ℂ) (hf : ContinuousOn f U)
    (hhol : DifferentiableOn ℂ f {z | z ∈ U ∧ f z ≠ 0}) :
    DifferentiableOn ℂ f U := by sorry

end LeblSCV.Pseudoconvex
