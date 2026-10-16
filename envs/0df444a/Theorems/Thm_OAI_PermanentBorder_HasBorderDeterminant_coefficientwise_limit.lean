-- Prove2me | Theorems.Thm_OAI_PermanentBorder_HasBorderDeterminant_coefficientwise_limit
-- name    : OAI.PermanentBorder.HasBorderDeterminant.coefficientwise_limit
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T23:17:25.117107+00:00
-- url     : https://prove2.me/theorems/5e9f046e-7219-43c6-ab91-913c04a86ab6
-- title:
--   Border determinantal representations of fixed size are closed under coefficientwise limits
-- statement:
--   Let $\sigma$ be a finite set and let $\mathbb{C}[x]$ denote the ring of complex polynomials in the variables $x=(x_v)_{v\in\sigma}$. For an exponent vector $\alpha\in\mathbb{N}^{\sigma}$ write $x^\alpha=\prod_{v\in\sigma}x_v^{\alpha_v}$ and $[x^\alpha]P$ for the coefficient of $x^\alpha$ in $P\in\mathbb{C}[x]$.
--
--   Given $n\in\mathbb{N}$ and complex $n\times n$ matrices $A_0$ and $A_v$ ($v\in\sigma$), the matrix $A_0+\sum_{v\in\sigma}x_vA_v$ has affine-linear entries and its determinant is a polynomial in $\mathbb{C}[x]$. A polynomial $p$ *has a border determinant of size $n$* if $n\ge 1$ and there are sequences of complex $n\times n$ matrices $A_0^{(k)}$ and $A_v^{(k)}$ ($v\in\sigma$, $k\in\mathbb{N}$) such that every coefficient converges: $[x^\alpha]\det\bigl(A_0^{(k)}+\sum_{v\in\sigma}x_vA_v^{(k)}\bigr)\to[x^\alpha]p$ as $k\to\infty$, for every $\alpha\in\mathbb{N}^{\sigma}$. Write $\overline{\mathcal{D}}_n$ for the set of such polynomials.
--
--   **Theorem.** Let $n\in\mathbb{N}$, let $(P_j)_{j\in\mathbb{N}}$ be a sequence of polynomials in $\mathbb{C}[x]$ and let $p\in\mathbb{C}[x]$. If every $P_j$ has a border determinant of size $n$ and the coefficients of $P_j$ converge to those of $p$, then $p$ has a border determinant of size $n$:
--
--   $$
--   \Bigl(P_j\in\overline{\mathcal{D}}_n\ \text{for all } j\in\mathbb{N}\Bigr)\ \text{ and }\ \Bigl(\lim_{j\to\infty}[x^\alpha]P_j=[x^\alpha]p\ \text{for all }\alpha\in\mathbb{N}^{\sigma}\Bigr)\ \Longrightarrow\ p\in\overline{\mathcal{D}}_n .
--   $$
--
--   The approximating matrices of the different $P_j$ may be completely unrelated: no bound on their entries and no uniform rate of convergence is assumed, and the matrix size stays exactly $n$.
--
--   In topological terms, $\overline{\mathcal{D}}_n$ is closed under coefficientwise convergence. This closure property lets degeneration arguments (replacing a polynomial by a limit of rescaled or substituted copies of it, for instance by its lowest-degree homogeneous part) stay inside the class of border determinants of a fixed size, so that lower bounds on the border determinantal size of the degeneration apply to the original polynomial.
--
--   **Formalization Note** Polynomials are `MvPolynomial σ ℂ` (abbreviated `Poly σ`) with `σ` a `Fintype`, exponent vectors are finitely supported functions `σ →₀ ℕ`, and the affine determinant is `affineMatrixPolynomial n A₀ A`. The predicate `HasBorderDeterminant n p` consists of the condition `0 < n` together with the existence of the approximating matrix sequences; all limits are taken along `atTop`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Algebra/Determinantal/BorderClosure.lean#L11-L49

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
open Filter
open scoped Topology

theorem OAI.PermanentBorder.HasBorderDeterminant.coefficientwise_limit
    {σ : Type*} [Fintype σ] {n : ℕ} {P : ℕ → Poly σ} {p : Poly σ}
    (hP : ∀ j, HasBorderDeterminant n (P j))
    (hp : ∀ d : σ →₀ ℕ,
      Tendsto (fun j => (P j).coeff d) atTop (𝓝 (p.coeff d))) :
    HasBorderDeterminant n p := by sorry
