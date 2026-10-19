-- Prove2me | Theorems.Thm_OAI_EuclideanRamsey_bilinear_orthonormal_trace
-- name    : OAI.EuclideanRamsey.bilinear_orthonormal_trace
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T02:02:05.351816+00:00
-- url     : https://prove2.me/theorems/322f408d-99c8-4ab8-8f42-bb0fe47b2e11
-- title:
--   The trace of a bilinear form does not depend on the orthonormal basis
-- statement:
--   Let $E$ be a real inner product space and let $B : E\times E\to\mathbb{R}$ be a continuous bilinear form. Let $(e_i)_{i\in I}$ and $(f_j)_{j\in J}$ be two orthonormal bases of $E$, indexed by finite sets $I$ and $J$. Then
--
--   $$
--   \sum_{i\in I} B(e_i,e_i) \;=\; \sum_{j\in J} B(f_j,f_j).
--   $$
--
--   Thus the trace $\operatorname{tr}B=\sum_i B(e_i,e_i)$ of a bilinear form on a finite-dimensional inner product space is well defined, independently of the orthonormal basis used to compute it. A typical application is to a Hessian $B=D^2h(x)$: the Laplacian $\Delta h(x)=\sum_i D^2h(x)[e_i,e_i]$ may be computed in any orthonormal basis.
--
--   **Formalization Note** $B$ has type `E →L[ℝ] E →L[ℝ] ℝ`, and the bases are `OrthonormalBasis ι ℝ E` and `OrthonormalBasis κ ℝ E` with `[Fintype ι] [Fintype κ]`; the existence of such a basis makes $E$ finite-dimensional. No symmetry of $B$ is assumed.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/EuclideanRamsey/Hessian.lean#L126-L152

import Mathlib
import Definitions.Def_EuclideanRamsey
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_TensorNecessity
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_TensorDescent
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_SmoothingKernel
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_Hessian

open OAI OAI.EuclideanRamsey
universe uDomain uCodomain uIndex uColor uAction
open scoped TensorProduct RealInnerProductSpace
open scoped BigOperators
open Real Filter Topology MeasureTheory Polynomial
open scoped BigOperators
open Matrix MeasureTheory
variable {E : Type uDomain} {ι : Type uIndex} {κ : Type uColor} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Fintype ι] [Fintype κ]

theorem OAI.EuclideanRamsey.bilinear_orthonormal_trace (B : E →L[ℝ] E →L[ℝ] ℝ)
    (e : OrthonormalBasis ι ℝ E) (f : OrthonormalBasis κ ℝ E) :
    ∑ i, B (e i) (e i) = ∑ j, B (f j) (f j) := by sorry
