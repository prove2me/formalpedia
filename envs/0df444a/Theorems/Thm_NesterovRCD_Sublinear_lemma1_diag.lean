-- Prove2me | Theorems.Thm_NesterovRCD_Sublinear_lemma1_diag
-- name    : NesterovRCD.Sublinear.lemma1_diag
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T13:22:13.798092+00:00
-- url     : https://prove2.me/theorems/65c6dc28-e4fe-4ebe-9665-872de8918dd4
-- title:
--   Lemma 1, last claim — $A\preceq n\cdot\mathrm{diag}\{A_{i,i}\}_{i=1}^n$
-- statement:
--   Let $A\in\mathbb R^{m\times m}$ be symmetric positive semidefinite. Then $A\preceq m\cdot\mathrm{diag}\{A_{1,1},\dots,A_{m,m}\}$, that is, for every $x\in\mathbb R^m$
--   $$\langle Ax,x\rangle\le m\sum_{j=1}^mA_{j,j}\,(x^{(j)})^2 .$$
--
--   This is the special case of Lemma 1 for the decomposition into one-dimensional subspaces, with $B_j=A_{j,j}$ and $L_j=1$. It explains why the sum of the coordinate Lipschitz constants is at most $n$ times larger than the global Lipschitz constant in the worst case.
--
--   **Formalization Note** The paper's dimension $n$ is $m$ here, and $A_{i,i}$ denotes the scalar diagonal entries.
-- source:
--   Nesterov, Efficiency of coordinate descent methods on huge-scale optimization problems, CORE Discussion Paper 2010/2, p. 4, Lemma 1 ("In particular")

import Mathlib

namespace NesterovRCD.Sublinear

open Matrix

theorem lemma1_diag {m : ℕ} (A : Matrix (Fin m) (Fin m) ℝ) (hA : A.PosSemidef) (x : Fin m → ℝ) :
    x ⬝ᵥ (A *ᵥ x) ≤ (m : ℝ) * ∑ j, A j j * x j ^ 2 := by sorry

end NesterovRCD.Sublinear
