-- Prove2me | Theorems.Thm_MasulloAudit_bounded_biorthogonal_system_unbounded_functionals
-- name    : MasulloAudit.bounded_biorthogonal_system_unbounded_functionals
-- status  : Proved
-- author  : @deleted
-- created : 2026-11-21T00:02:06.342317+00:00
-- url     : https://prove2.me/theorems/fece7c79-3a17-4cb3-9bcd-3f1334406333
-- title:
--   Bounded systems bounded away from 0 can have unbounded biorthogonal functionals
-- statement:
--   For every real $M$ there are two vectors $x_1,x_2\in\mathbb R^2$ (Euclidean norm) with
--
--   $$
--   1\le\|x_1\|\le2,\qquad 1\le\|x_2\|\le2,
--   $$
--
--   which admit a biorthogonal system of continuous linear functionals $g_1,g_2$ (that is, $g_i(x_j)=\delta_{ij}$), such that every functional $f$ with $f(x_1)=0$ and $f(x_2)=1$, in particular the biorthogonal functional $g_2$, satisfies $\|f\|>M$.
--
--   This is a counterexample to the inference in Terminology 10.2.1.2(2) of Masullo's draft (p. 444): that a "regular" (Markushevich) basis, whose vectors are bounded and bounded away from $0$, has bounded biorthogonal functionals. Being bounded and bounded away from zero does not bound the biorthogonal functionals. That inference supplies the uniform constant used after (10.3.1.18) (p. 451) and the two-sided bound (10.4.2.24) (p. 463).
--
--   **Formalization Note.** The example is $x_1=(1,0)$, $x_2=(1,\varepsilon)$ with $\varepsilon=1/(|M|+1)$. The statement is finite-dimensional on purpose: it isolates the logical step, independently of the function spaces of the draft.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, Terminology 10.2.1.2(2) (p. 444), proof of Theorem 10.3.1.1 after eq. (10.3.1.18) (p. 451), and eq. (10.4.2.24) in the proof of Theorem 10.4.2.8 (p. 463).

import Mathlib.Analysis.InnerProductSpace.PiL2

namespace MasulloAudit

theorem bounded_biorthogonal_system_unbounded_functionals (M : ℝ) :
    ∃ x₁ x₂ : EuclideanSpace ℝ (Fin 2), 1 ≤ ‖x₁‖ ∧ ‖x₁‖ ≤ 2 ∧ 1 ≤ ‖x₂‖ ∧ ‖x₂‖ ≤ 2 ∧
      (∃ g₁ g₂ : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ,
        g₁ x₁ = 1 ∧ g₁ x₂ = 0 ∧ g₂ x₁ = 0 ∧ g₂ x₂ = 1) ∧
      ∀ f : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ, f x₁ = 0 → f x₂ = 1 → M < ‖f‖ := by sorry

end MasulloAudit
