-- Prove2me | Theorems.Thm_Module_Dual_exists_trace_eq
-- name    : Module.Dual.exists_trace_eq
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-26T16:48:21.893093+00:00
-- url     : https://prove2.me/theorems/a30bed17-0513-4622-8869-943ad8046f43
-- title:
--   Every linear functional on $\mathbb{R}^{n\times n}$ is $A \mapsto \operatorname{tr}(Y^{\mathsf T} A)$
-- statement:
--   Let $n$ be a finite type with decidable equality. For every linear functional $\varphi$ on the space of real $n \times n$ matrices there is a matrix $Y$ with
--
--   $$
--   \varphi(A) \;=\; \operatorname{tr}\big(Y^{\mathsf T} A\big) \qquad \text{for all } A \in \mathbb{R}^{n \times n} .
--   $$
--
--   The witness is $Y_{ij} = \varphi(E_{ij})$, the values of $\varphi$ on the matrix units.
--
--   The trace pairing $\langle Y, A \rangle = \operatorname{tr}(Y^{\mathsf T} A)$ is the inner
--   product in which semidefinite programming is written, so this is the representation result that
--   turns an abstract dual object into an SDP dual *variable*. Every derivation of an SDP dual --
--   and every separation argument that produces a functional on matrix space and then needs a
--   matrix certificate -- passes through it.
--
--   **Formalization Note** The proof expands $A$ as $\sum_{ij} A_{ij} E_{ij}$ with
--   `Matrix.matrix_eq_sum_single`, pushes $\varphi$ through the sum by linearity, and matches the
--   result against the double sum defining $\operatorname{tr}(Y^{\mathsf T} A)$ after
--   `Finset.sum_comm`.
-- source:
--   Carried as an internal support lemma, with this exact statement and proof, in twelve accepted submissions across ten missions of the OR Formalization Drive (e.g. https://prove2.me/submissions/3c55ced4-4944-4de2-ba43-8110d2682db1); published here once so that it can be imported. The trace (Frobenius) pairing on matrices; standard in semidefinite programming duality.

import Mathlib

open Matrix

theorem Module.Dual.exists_trace_eq {n : Type*} [Fintype n] [DecidableEq n]
    (φ : Module.Dual ℝ (Matrix n n ℝ)) : ∃ Y : Matrix n n ℝ, ∀ A, φ A = (Yᵀ * A).trace := by sorry
