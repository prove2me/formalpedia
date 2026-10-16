-- Prove2me | Theorems.Thm_OAI_PermanentBorder_HasBorderDeterminant_lowest_homogeneousComponent
-- name    : OAI.PermanentBorder.HasBorderDeterminant.lowest_homogeneousComponent
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T23:19:59.683647+00:00
-- url     : https://prove2.me/theorems/7a462d16-ebb4-48df-a56f-789c37036229
-- title:
--   If all homogeneous components of degree below $r$ vanish, the degree-$r$ component inherits a border determinant of size $n$
-- statement:
--   Let $\sigma$ be a finite set and $\mathbb{C}[x]$ the ring of complex polynomials in $x=(x_v)_{v\in\sigma}$. Write $[x^\alpha]P$ for the coefficient of $x^\alpha=\prod_v x_v^{\alpha_v}$ ($\alpha\in\mathbb{N}^{\sigma}$) in $P$, and $q_k$ for the homogeneous component of degree $k$ of $q$, i.e. the sum of its terms of total degree $k$. A polynomial $p$ *has a border determinant of size $n$* if $n\ge1$ and there are sequences of complex $n\times n$ matrices $A_0^{(k)}$ and $A_v^{(k)}$ ($v\in\sigma$, $k\in\mathbb{N}$) such that $[x^\alpha]\det\bigl(A_0^{(k)}+\sum_{v}x_vA_v^{(k)}\bigr)\to[x^\alpha]p$ as $k\to\infty$ for every $\alpha\in\mathbb{N}^{\sigma}$. Write $\overline{\mathcal{D}}_n$ for the set of such polynomials.
--
--   **Theorem.** Let $n,r\in\mathbb{N}$ and let $q\in\mathbb{C}[x]$ have a border determinant of size $n$. If $q_k=0$ for every $k<r$, then the homogeneous component $q_r$ also has a border determinant of size $n$:
--
--   $$
--   q\in\overline{\mathcal{D}}_n\quad\text{and}\quad q_k=0\ \text{ for all } k<r\qquad\Longrightarrow\qquad q_r\in\overline{\mathcal{D}}_n .
--   $$
--
--   No assumption $q_r\neq0$ is made, and for $r=0$ the hypothesis on lower components is empty and the conclusion concerns the constant term $q_0$. When $q_r\neq0$, it is the lowest-degree part, or initial form, of $q$ at the origin.
--
--   This is the degeneration principle that border determinantal size does not increase when a polynomial is replaced by its initial form. Combined with invariance under translations $x\mapsto a+x$, it reduces lower bounds on the border determinantal size of a polynomial to lower bounds for its homogeneous initial form at a chosen point $a$, where homogeneity and smoothness of the form can be exploited.
--
--   **Formalization Note** Homogeneous components are Mathlib's `homogeneousComponent k q`, and the hypothesis reads `∀ j < r, homogeneousComponent j q = 0`. The predicate `HasBorderDeterminant n p` (which includes `0 < n`) asks for coefficientwise convergence of `affineMatrixPolynomial n (A₀ k) (A k)` to `p` along `atTop`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Algebra/Determinantal/InitialForm.lean#L104-L123

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
import Definitions.Def_OAI_Algebra_Determinantal_BorderPolars
import Definitions.Def_OAI_Algebra_Determinantal_InitialForm

open OAI OAI.PermanentBorder
open MvPolynomial Filter
open scoped Topology

theorem OAI.PermanentBorder.HasBorderDeterminant.lowest_homogeneousComponent
    {σ : Type*} [Fintype σ] {n r : ℕ} {q : Poly σ}
    (hb : HasBorderDeterminant n q)
    (hlow : ∀ j < r, homogeneousComponent j q = 0) :
    HasBorderDeterminant n (homogeneousComponent r q) := by sorry
