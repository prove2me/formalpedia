-- Prove2me | Theorems.Thm_OAI_DirectCrouzeix_isUnit_resolvent_of_not_mem
-- name    : OAI.DirectCrouzeix.isUnit_resolvent_of_not_mem
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T05:25:58.025986+00:00
-- url     : https://prove2.me/theorems/3040e185-e434-4f05-86b4-c85f7cb28188
-- title:
--   Points outside the numerical range lie in the resolvent set
-- statement:
--   Let $n\ge0$ be an integer and $A$ a complex $n\times n$ matrix. Equip $\mathbb{C}^n$ with the inner product $\langle x,y\rangle=\sum_i\overline{x_i}\,y_i$ and the Euclidean norm $\|x\|=\langle x,x\rangle^{1/2}$, and let
--   $$W(A)=\{\langle u,Au\rangle:\ u\in\mathbb{C}^n,\ \|u\|=1\}$$
--   be the numerical range of $A$. If $z\in\mathbb{C}$ does not belong to $W(A)$, then $zI-A$ is invertible:
--   $$z\notin W(A)\quad\Longrightarrow\quad zI-A\ \text{is an invertible element of the matrix ring } M_n(\mathbb{C}).$$
--
--   Equivalently, every eigenvalue of $A$ lies in its numerical range. Consequently the resolvent $(zI-A)^{-1}$ is defined at every point outside $W(A)$, in particular on the boundary of any region containing $W(A)$ in its interior, which is where resolvent integrals and boundary kernels for the polynomial calculus of $A$ are evaluated.
--
--   **Formalization Note** Invertibility is `IsUnit (z • 1 - A)` in the ring `Matrix (Fin n) (Fin n) ℂ`. The numerical range is `numericalRange A`, which uses the action of $A$ on `EuclideanSpace ℂ (Fin n)` through `Matrix.toEuclideanCLM`. For $n=0$ the statement is trivially true, since then $W(A)$ is empty and the empty matrix is invertible.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/DirectCrouzeix/Resolvent.lean#L130-L142

import Mathlib
import Definitions.Def_DirectCrouzeix
import Definitions.Def_OAI_Analysis_DirectCrouzeix_PositiveBlocks
import Definitions.Def_OAI_Analysis_DirectCrouzeix_Resolvent

open OAI OAI.DirectCrouzeix
open scoped Matrix Matrix.Norms.L2Operator Kronecker
open scoped MatrixOrder ComplexOrder

theorem OAI.DirectCrouzeix.isUnit_resolvent_of_not_mem {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    {z : ℂ} (hz : z ∉ numericalRange A) : IsUnit (z • 1 - A) := by sorry
