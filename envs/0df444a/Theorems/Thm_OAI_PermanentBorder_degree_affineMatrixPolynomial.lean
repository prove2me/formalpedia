-- Prove2me | Theorems.Thm_OAI_PermanentBorder_degree_affineMatrixPolynomial
-- name    : OAI.PermanentBorder.degree_affineMatrixPolynomial
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T23:16:17.399211+00:00
-- url     : https://prove2.me/theorems/225f2f65-b42d-414d-9c28-3634fd6bc703
-- title:
--   The determinant of an $n\times n$ matrix of affine-linear forms has degree at most $n$
-- statement:
--   Let $\sigma$ be a finite set of variables, $n\in\mathbb{N}$, and let $A_0$ and $A_v$ ($v\in\sigma$) be complex $n\times n$ matrices. Consider the $n\times n$ matrix of affine-linear forms $A_0+\sum_{v\in\sigma}X_vA_v$, whose $(i,j)$ entry is $(A_0)_{ij}+\sum_v(A_v)_{ij}X_v$. Its determinant is a polynomial in $\mathbb{C}[X_v : v\in\sigma]$ of total degree at most $n$:
--   $$
--   \deg\,\det\Big(A_0+\sum_{v\in\sigma}X_v\,A_v\Big)\le n .
--   $$
--
--   Consequently, a polynomial represented exactly as the determinant of an $n\times n$ matrix of affine-linear forms has degree at most $n$. Combined with the closure of bounded-exponent polynomials under coefficientwise limits, this confines border determinantal approximations of size $n$ to a fixed finite-dimensional space of polynomials.
--
--   **Formalization Note** The polynomial is `affineMatrixPolynomial n A₀ A`, and the degree is `totalDegree`. For $n=0$ the determinant of the empty matrix is $1$, of degree $0$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Algebra/Determinantal/Model.lean#L244-L258

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
variable {σ : Type*} [Fintype σ]

theorem OAI.PermanentBorder.degree_affineMatrixPolynomial (n : ℕ)
    (A₀ : Matrix (Fin n) (Fin n) ℂ) (A : σ → Matrix (Fin n) (Fin n) ℂ) :
    (affineMatrixPolynomial n A₀ A).totalDegree ≤ n := by sorry
