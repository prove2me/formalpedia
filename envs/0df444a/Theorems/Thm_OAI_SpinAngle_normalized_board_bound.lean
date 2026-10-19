-- Prove2me | Theorems.Thm_OAI_SpinAngle_normalized_board_bound
-- name    : OAI.SpinAngle.normalized_board_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T07:16:51.684842+00:00
-- url     : https://prove2.me/theorems/895a068c-b27a-4e51-9b47-8ec0f563afdc
-- title:
--   Board bound: the squared norm of a tensor product of normalized cell matrices is at most $\prod_i(|C|/o_i)^{o_i}$
-- statement:
--   Let $n$, $R$ and $C$ be finite sets with $C$ nonempty, and let $W\subseteq R\times C$ be a set of cells; for a row $i\in R$ let $o_i=|\{j\in C:(i,j)\in W\}|$ be the number of cells of $W$ in that row. A density matrix on $\mathbb{C}^n$ is a positive semidefinite $n\times n$ complex matrix of trace $1$. Let $(r_j)_{j\in C}$ and $(s_i)_{i\in R}$ be density matrices and let $\bar r=\frac{1}{|C|}\sum_{j\in C}r_j$ be the column average. For positive semidefinite $x=\sum_\lambda\lambda P_\lambda$ write $\sqrt{x}=\sum_\lambda\sqrt{\lambda}\,P_\lambda$ and $x^{-1/2}=\sum_{\lambda>0}\lambda^{-1/2}P_\lambda$ (the pseudo-inverse square root). Define the missing-cell factor
--   $$\varphi(W)=\prod_{i\in R,\ o_i\ge1}\Big(\frac{|C|}{o_i}\Big)^{o_i},$$
--   so rows without cells contribute the factor $1$.
--
--   **Theorem.** With $\|\cdot\|$ the operator norm on $(\mathbb{C}^n)^{\otimes W}$,
--   $$\Big\|\bigotimes_{(i,j)\in W}\sqrt{r_j}\;\bar r^{-1/2}\sqrt{s_i}\Big\|^{2}\le\varphi(W).$$
--
--   The tensor product has one factor per cell, built from the density of the cell's column, the inverse square root of the column average, and the density of the cell's row. A full row ($o_i=|C|$) contributes the factor $1$, so for $W=R\times C$ the bound is $1$; and since $(|C|/o_i)^{o_i}\le e^{|C|-o_i}$, one has $\varphi(W)\le e^{|R||C|-|W|}$, i.e. the bound is at most exponential in the number of missing cells. The estimate controls the cross term between column and row product states in the angle bound for type projections on a board of cells.
--
--   **Formalization Note** $\varphi(W)$ is `missingCellProductFactor (Fintype.card C) (missingInRow W)`, the product over all rows of `missingCellFactor m b`, which is `(m/(m-b))^(m-b)` if `b < m` and `1` otherwise, with $m=|C|$ and $b=m-o_i$ the number of missing cells of the row; this equals $(|C|/o_i)^{o_i}$ for $o_i\ge1$ and $1$ for $o_i=0$. Densities are the structure `MatrixAnalysis.Density`, $\bar r$ is `average r`, the factors are `root` and `invRoot` (continuous functional calculus), the tensor product is `TensorMatrix.tensor` over the subtype of cells of `W`, and the norm is the operator norm of `Matrix.Norms.L2Operator`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/RepresentationTheory/SpinAngle/Core.lean#L4278-L4294

import Mathlib
import Definitions.Def_SpinAngle
import Definitions.Def_OAI_RepresentationTheory_SpinAngle_Core

open OAI OAI.SpinAngle
open scoped BigOperators ComplexConjugate InnerProductSpace
open scoped BigOperators ComplexConjugate InnerProductSpace Matrix
open scoped Matrix ComplexOrder
open scoped TensorProduct InnerProductSpace BigOperators
open scoped BigOperators ComplexConjugate
open scoped InnerProductSpace
open scoped TensorProduct InnerProductSpace ComplexOrder
open scoped BigOperators
open scoped InnerProductSpace ComplexOrder BigOperators
open scoped InnerProductSpace BigOperators ComplexOrder
open scoped BigOperators
open scoped BigOperators
open MeasureTheory TopologicalSpace Set
open scoped BigOperators
open scoped BigOperators
open Set
open scoped BigOperators Matrix.Norms.L2Operator MatrixOrder ComplexOrder
open scoped BigOperators
open MatrixAnalysis TensorMatrix
variable {n R C : Type*} [contextInstance3979_25 : Fintype n] [contextInstance3979_37 : DecidableEq n]
  [contextInstance3980_2 : Fintype R] [contextInstance3980_14 : DecidableEq R] [contextInstance3980_30 : Fintype C] [contextInstance3980_42 : DecidableEq C] [contextInstance3980_58 : Nonempty C]

theorem OAI.SpinAngle.normalized_board_bound (W : Finset (R × C))
    (r : C → Density n) (s : R → Density n) :
    ‖tensor (fun w : W => root (r w.val.2).matrix *
      invRoot (average r) * root (s w.val.1).matrix)‖ ^ 2 ≤
        missingCellProductFactor (Fintype.card C) (missingInRow W) := by sorry
