-- Prove2me | Theorems.Thm_HeathcoteUnbounded_selfAdjoint_unbounded_domain
-- name    : HeathcoteUnbounded.selfAdjoint_unbounded_domain
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-13T14:34:37.500915+00:00
-- url     : https://prove2.me/theorems/77ec1fe5-c9c8-41bb-bcad-7cc40e6395bb
-- title:
--   Unbounded self-adjoint operators are defined only on dense proper subspaces
-- statement:
--   Let $\mathcal H$ be a complex Hilbert space and $A$ a (partially defined) linear operator on $\mathcal H$ with domain $D(A)$. Suppose $A$ is self-adjoint, $A=A^*$ (in particular $D(A)=D(A^*)$), and unbounded, i.e. there is no $k\in\mathbb R$ with
--
--   $$\|A\psi\|\le k\,\|\psi\|\quad\text{for all }\psi\in D(A).$$
--
--   Then
--
--   1. $D(A)$ is dense in $\mathcal H$, and
--   2. $D(A)\ne\mathcal H$.
--
--   This is the source's consequence of the Hellinger–Toeplitz theorem together with the requirement that the adjoint be a genuine (single-valued) operator: unbounded observables of quantum mechanics are defined only on dense subspaces.
--
--   **Formalization Note** Operators are Mathlib's `LinearPMap` (`H →ₗ.[ℂ] H`), and self-adjointness is `IsSelfAdjoint` for the adjoint `A†`.
-- source:
--   A. Heathcote, "Unbounded Operators and the Incompleteness of Quantum Mechanics", Philosophy of Science 57 (1990), 523–534, p. 2, eqs. (1)–(2), footnotes 1–2

import Mathlib

namespace HeathcoteUnbounded

theorem selfAdjoint_unbounded_domain {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A)
    (hunb : ¬ ∃ k : ℝ, ∀ ψ : A.domain, ‖A ψ‖ ≤ k * ‖(ψ : H)‖) :
    Dense (A.domain : Set H) ∧ A.domain ≠ ⊤ := by sorry

end HeathcoteUnbounded
