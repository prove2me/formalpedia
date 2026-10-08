-- Prove2me | Theorems.Thm_LLLFactor_Reduction_step_preserves_basis
-- name    : LLLFactor.Reduction.step_preserves_basis
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:28:39.321438+00:00
-- url     : https://prove2.me/theorems/79f4e108-4ebe-417e-8d70-65fd4268f81d
-- title:
--   (1.15), p. 519 — every step of the algorithm keeps b₁, …, bₙ a basis for the same lattice L
-- statement:
--   Let $b_1,\dots,b_n\in\mathbb R^n$ be linearly independent and let $k$ be a subscript. If one step of the basis reduction algorithm (1.15) (case 1 or case 2, including the achievement of (1.18) and the loop of case 2) leads from the state $(b,k)$ to the state $(b',k')$, then $b'_1,\dots,b'_n$ are linearly independent and
--   $$\sum_{i=1}^n\mathbb Z b'_i=\sum_{i=1}^n\mathbb Z b_i .$$
--
--   This is the paper's claim that "in the course of the algorithm the vectors $b_1,\dots,b_n$ will be changed several times, but always in such a way that they form a basis for $L$", and it is what makes the output of the algorithm a basis of the *input* lattice.
--
--   **Formalization Note.** A step is the relation `Step` of the definitions module; it allows either nearest integer at a tie.
-- source:
--   Lenstra, Lenstra, Lovász, Factoring polynomials with rational coefficients, Math. Ann. 261 (1982), p. 519, (1.15)

import Mathlib
import Definitions.Def_LLLFactor_Reduction_Algorithm

namespace LLLFactor.Reduction

theorem step_preserves_basis {n : ℕ} (b b' : Fin n → LLLFactor.RedBasis.Vec n) (k k' : ℕ)
    (hb : LinearIndependent ℝ b) (hstep : Step (b, k) (b', k')) :
    LinearIndependent ℝ b' ∧ LLLFactor.RedBasis.latticeOf b' = LLLFactor.RedBasis.latticeOf b := by sorry

end LLLFactor.Reduction
