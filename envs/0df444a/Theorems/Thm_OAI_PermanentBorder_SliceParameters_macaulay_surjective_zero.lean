-- Prove2me | Theorems.Thm_OAI_PermanentBorder_SliceParameters_macaulay_surjective_zero
-- name    : OAI.PermanentBorder.SliceParameters.macaulay_surjective_zero
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T22:59:05.589766+00:00
-- url     : https://prove2.me/theorems/c5124616-c062-40eb-aa64-6e35a928f0a5
-- title:
--   A surjective Macaulay matrix certifies that a homogeneous system has only the trivial zero
-- statement:
--   Let $K$ be a field, $\sigma$ and $\iota$ finite sets, and $F=(F_i)_{i\in\iota}$ polynomials in $K[X_j : j\in\sigma]$ with $F_i$ homogeneous of degree $e_i\in\mathbb{N}$. Let $D\in\mathbb{N}$, and let $M_D$ be the degree-$D$ Macaulay matrix of $F$. Its rows are indexed by the exponent vectors $s$ of total degree $D$, its columns by the pairs $(i,t)$ with $i\in\iota$ and $t$ an exponent vector of total degree $D-e_i$ (computed in $\mathbb{Z}$, so there are no such columns when $e_i>D$), and its entry $M_D[s,(i,t)]$ is the coefficient of $X^s$ in $F_i\,X^t$. If the linear map $b\mapsto M_Db$ is surjective, then $0$ is the only common zero of the $F_i$ in $K^\sigma$:
--   $$
--   \forall\,y\in K^\sigma:\qquad F_i(y)=0\ \text{for all } i\in\iota\ \Longrightarrow\ y=0 .
--   $$
--
--   This is the easy direction of the Macaulay-matrix criterion. A single surjective Macaulay matrix certifies that a homogeneous system has no nontrivial solution, i.e. no projective zero. Surjectivity of a matrix is detected by a nonvanishing determinant, so such certificates can be propagated along families of systems and transferred between fields.
--
--   **Formalization Note** The matrix is `macaulayMatrix (fun i => (e i : ℤ)) F D` with the natural degrees and $D$ cast to integers.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Algebra/Determinantal/SliceCertificates.lean#L25-L42

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

open OAI OAI.PermanentBorder OAI.PermanentBorder.SliceParameters
open MvPolynomial

theorem OAI.PermanentBorder.SliceParameters.macaulay_surjective_zero {K σ ι : Type*} [Field K] [Fintype σ] [Fintype ι]
    (F : ι → MvPolynomial σ K) (e : ι → ℕ) (hh : ∀ i, (F i).IsHomogeneous (e i))
    (D : ℕ) (hM : Function.Surjective (macaulayMatrix (fun i => (e i : ℤ)) F D).mulVec)
    (y : σ → K) (hy : ∀ i, eval y (F i) = 0) : y = 0 := by sorry
