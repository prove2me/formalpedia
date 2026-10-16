-- Prove2me | Theorems.Thm_OAI_PermanentBorder_support_subset_cube_of_limit
-- name    : OAI.PermanentBorder.support_subset_cube_of_limit
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T23:14:45.34722+00:00
-- url     : https://prove2.me/theorems/429bdd2c-48a7-458b-b8ad-7e37dcbddbc1
-- title:
--   Coefficientwise limits of polynomials keep every exponent bounded by $n$
-- statement:
--   Let $\sigma$ be a finite set of variables, $n\in\mathbb{N}$, and let
--   $$
--   C_n=\{d\in\mathbb{N}^\sigma : d_i\le n\ \text{for all } i\in\sigma\}
--   $$
--   be the cube of exponent vectors in which every exponent is at most $n$. For a complex polynomial $p$ in the variables $X_i$, $i\in\sigma$, write $[X^d]\,p$ for its coefficient of $X^d=\prod_iX_i^{d_i}$ and $\operatorname{supp}p=\{d : [X^d]\,p\ne0\}$. Let $(P_j)_{j\in\mathbb{N}}$ be a sequence of such polynomials and $p$ another one. Then
--   $$
--   \Big(\operatorname{supp}P_j\subseteq C_n\ \text{for all } j\Big)\ \text{and}\ \Big(\lim_{j\to\infty}[X^d]\,P_j=[X^d]\,p\ \text{for all } d\in\mathbb{N}^\sigma\Big)\quad\Longrightarrow\quad \operatorname{supp}p\subseteq C_n .
--   $$
--
--   So the finite-dimensional space of polynomials with all exponents at most $n$ is closed under coefficientwise limits. This allows coefficients of linear images of such polynomials to be written as finite sums over $C_n$ and passed to the limit. For example, it applies to limits of determinants $\det\big(A_0(j)+\sum_vX_vA_v(j)\big)$ of $n\times n$ matrices, whose exponents are at most $n$, as in the definition of border determinantal representations.
--
--   **Formalization Note** $C_n$ is `exponentCube n`, the finite set `Finset.Iic` of the constant exponent vector $n$, and convergence is `Tendsto` along `atTop` in $\mathbb{C}$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Algebra/Determinantal/Model.lean#L200-L214

import Mathlib
import Definitions.Def_SmoothInitialForm
import Definitions.Def_OAI_Algebra_Determinantal_Multigraded
import Definitions.Def_OAI_Algebra_Determinantal_LinearForms
import Definitions.Def_OAI_Algebra_Determinantal_PointBounds
import Definitions.Def_OAI_Algebra_Determinantal_ProjectiveCounts
import Definitions.Def_OAI_Algebra_Determinantal_KernelCharts
import Definitions.Def_OAI_Algebra_Determinantal_SchurDifferentials
import Definitions.Def_OAI_Algebra_Determinantal_SchurLifts
import Definitions.Def_OAI_Algebra_Determinantal_BilinearCounts
import Definitions.Def_OAI_Algebra_Determinantal_RegularSections
import Definitions.Def_OAI_Algebra_Determinantal_SmoothSlices
import Definitions.Def_OAI_Algebra_Determinantal_SliceCertificates
import Definitions.Def_OAI_Algebra_Determinantal_GenericPolars
import Definitions.Def_OAI_Algebra_Determinantal_RankTransfer
import Definitions.Def_OAI_Algebra_Determinantal_Model

open OAI OAI.PermanentBorder
open MvPolynomial Filter
open scoped Topology
variable {σ τ : Type*} [Fintype σ]

theorem OAI.PermanentBorder.support_subset_cube_of_limit {P : ℕ → Poly σ} {p : Poly σ} {n : ℕ}
    (hP : ∀ j, (P j).support ⊆ exponentCube n)
    (hp : ∀ d, Tendsto (fun j => (P j).coeff d) atTop (𝓝 (p.coeff d))) :
    p.support ⊆ exponentCube n := by sorry
