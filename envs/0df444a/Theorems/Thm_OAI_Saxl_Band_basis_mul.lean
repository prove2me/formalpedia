-- Prove2me | Theorems.Thm_OAI_Saxl_Band_basis_mul
-- name    : OAI.Saxl.Band.basis_mul
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T00:04:35.842196+00:00
-- url     : https://prove2.me/theorems/1c537f2e-2ad8-481e-b1c0-4cffe46ab811
-- title:
--   Products of the four basis matrices $I$, $Z$, $X$, $J$ are nonzero multiples of basis matrices
-- statement:
--   Consider the following four complex $2\times2$ matrices:
--   $$B_0=\begin{pmatrix}1&0\\0&1\end{pmatrix},\quad B_1=\begin{pmatrix}1&0\\0&-1\end{pmatrix},\quad B_2=\begin{pmatrix}0&1\\1&0\end{pmatrix},\quad B_3=\begin{pmatrix}0&1\\-1&0\end{pmatrix}.$$
--   We also write $I=B_0$, $Z=B_1$, $X=B_2$ and $J=B_3$. Call a matrix $Y\in\mathbb{C}^{2\times2}$ a *scaled basis matrix* if $Y=c\,B_k$ for some nonzero scalar $c\in\mathbb{C}$ and some $k\in\{0,1,2,3\}$.
--
--   **Theorem.** For all $i,j\in\{0,1,2,3\}$ the product $B_iB_j$ is a scaled basis matrix: there are $c\in\mathbb{C}\setminus\{0\}$ and $k\in\{0,1,2,3\}$ with
--   $$B_iB_j=c\,B_k.$$
--
--   Equivalently, the set of nonzero multiples of $B_0,\dots,B_3$ is closed under matrix multiplication. This is the algebraic input for evaluating ordered products of alternating sums of these matrices along the columns of a Young diagram with at most four rows: every such product is again a nonzero multiple of a single basis matrix, which is what makes a certain matrix-chain pairing nonzero.
--
--   **Formalization Note** The matrices are `Band.basis 0`, ..., `Band.basis 3` of type `Matrix (Fin 2) (Fin 2) ℂ` (the definition sends every index $\ge3$ to $B_3$, but only indices `i.val` with `i : Fin 4` occur), and "scaled basis matrix" is the predicate `Band.ScaledBasis`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/RepresentationTheory/Saxl/BandMatrices.lean#L181-L246

import Mathlib
import Definitions.Def_Saxl
import Definitions.Def_OAI_RepresentationTheory_Saxl_Basic
import Definitions.Def_OAI_RepresentationTheory_Saxl_Polytabloid
import Definitions.Def_OAI_RepresentationTheory_Saxl_SpechtSubmodule
import Definitions.Def_OAI_RepresentationTheory_Saxl_SpechtDuality
import Definitions.Def_OAI_RepresentationTheory_Saxl_TableauTransport
import Definitions.Def_OAI_RepresentationTheory_Saxl_StaircaseTensor
import Definitions.Def_OAI_RepresentationTheory_Saxl_HighProjection
import Definitions.Def_OAI_RepresentationTheory_Saxl_CoordinateSector
import Definitions.Def_OAI_RepresentationTheory_Saxl_PositionSplit
import Definitions.Def_OAI_RepresentationTheory_Saxl_BandFactorization
import Definitions.Def_OAI_RepresentationTheory_Saxl_PathAlternation
import Definitions.Def_OAI_RepresentationTheory_Saxl_BandMatrices

open OAI OAI.Saxl OAI.Saxl.Band
open scoped TensorProduct
universe uA

theorem OAI.Saxl.Band.basis_mul (i j : Fin 4) : ScaledBasis (basis i.val * basis j.val) := by sorry
