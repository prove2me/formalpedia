-- Prove2me | Theorems.Thm_OAI_GAD_det_linearDeriv
-- name    : OAI.GAD.det_linearDeriv
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T22:04:54.941782+00:00
-- url     : https://prove2.me/theorems/b1286516-ecb4-49f2-930e-b1c5fd64c292
-- title:
--   Jacobi's formula: the differential of the determinant is $H\mapsto\operatorname{tr}(H\operatorname{adj}A)$
-- statement:
--   Let $\iota$ be a finite index set and let $A,H\in\mathbb{C}^{\iota\times\iota}$ be square complex matrices. Regard the determinant as a multilinear function of the rows of a matrix, and for $i\in\iota$ let $A^{(i\leftarrow H)}$ be the matrix obtained from $A$ by replacing its $i$-th row with the $i$-th row of $H$. The linear derivative of this multilinear map at $A$ in the direction $H$ is $\sum_{i}\det A^{(i\leftarrow H)}$, and the theorem identifies it:
--
--   $$
--   \sum_{i\in\iota}\det A^{(i\leftarrow H)}=\operatorname{tr}\bigl(H\operatorname{adj}(A)\bigr),
--   $$
--
--   where $\operatorname{adj}(A)$ is the adjugate of $A$, the transpose of its cofactor matrix.
--
--   Since the determinant is a continuous multilinear map, the left-hand side is its Fréchet derivative at $A$ applied to $H$. The theorem is therefore Jacobi's formula $D\det(A)[H]=\operatorname{tr}(H\operatorname{adj}A)$, valid for every matrix $A$, singular or not. It is the starting point for differentiating determinants, inverses and log-determinants along curves of matrices.
--
--   **Formalization Note** `detMultilinear` is `Matrix.det` packaged as a `ContinuousMultilinearMap ℂ (fun _ : ι ↦ ι → ℂ) ℂ` in the rows, and `ContinuousMultilinearMap.linearDeriv` at $A$ applied to $H$ is the sum over $i$ of the map evaluated with the $i$-th argument replaced by the $i$-th argument of $H$. The index type carries `Fintype` and `DecidableEq` instances.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/AmplitudeDamping/MatrixDifferentiation.lean#L22-L36

import Mathlib
import Definitions.Def_AmplitudeDamping
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_Channel
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_MatrixDifferentiation

open OAI OAI.GAD
universe u_1 u_2
open scoped BigOperators
open Matrix
variable {ι : Type u_1} [Fintype ι] [DecidableEq ι]

theorem OAI.GAD.det_linearDeriv (A H : Matrix ι ι ℂ) :
    detMultilinear.linearDeriv A H = Matrix.trace (H * A.adjugate) := by sorry
