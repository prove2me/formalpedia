-- Prove2me | Theorems.Thm_OAI_MatchingSmoothing_trace_square_compression_le
-- name    : OAI.MatchingSmoothing.trace_square_compression_le
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T04:43:26.815395+00:00
-- url     : https://prove2.me/theorems/45298b65-2b61-49a2-9c98-90cde742542a
-- title:
--   Compressing a symmetric operator to a subspace does not increase the trace of its square
-- statement:
--   Let $E$ be a finite-dimensional real inner product space and let $A:E\to E$ be a symmetric linear operator, i.e. $\langle Ax,y\rangle=\langle x,Ay\rangle$ for all $x,y\in E$. Let $W\subseteq E$ be a linear subspace, let $P_W:E\to W$ be the orthogonal projection onto $W$, and let
--
--   $$
--   A_W=P_W\circ A|_W:\;W\to W,\qquad A_Ww=P_W(Aw),
--   $$
--
--   be the compression of $A$ to $W$. Then
--
--   $$
--   \operatorname{tr}_W\big(A_W^{2}\big)\;\le\;\operatorname{tr}_E\big(A^{2}\big),
--   $$
--
--   where $\operatorname{tr}_W$ and $\operatorname{tr}_E$ are the traces of linear operators on $W$ and on $E$.
--
--   For a symmetric operator, $\operatorname{tr}(A^2)$ is the sum of the squares of its eigenvalues (the squared Hilbert–Schmidt norm), so the inequality says that this quantity can only decrease when the operator is compressed to a subspace. It is used to transfer a trace bound for a kernel acting on all functions of perfect matchings to the compression of that kernel to the orthogonal complement of the low-degree polynomials.
--
--   **Formalization Note** The compression is `compression A W`, defined as `W.orthogonalProjectionOnto` composed with `A` restricted to `W` via `W.subtype`. The traces are `LinearMap.trace` over the reals on `W` and on `E`, and $A^2$ is the operator product `A * A`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/MatchingPSD/SpectralContraction.lean#L36-L65

import Mathlib
import Definitions.Def_MatchingPSD
import Definitions.Def_OAI_Combinatorics_MatchingPSD_EdgeProducts
import Definitions.Def_OAI_Combinatorics_MatchingPSD_Pairings
import Definitions.Def_OAI_Combinatorics_MatchingPSD_RepresentationDimension
import Definitions.Def_OAI_Combinatorics_MatchingPSD_ColoringCounts
import Definitions.Def_OAI_Combinatorics_MatchingPSD_TransitionMatrices
import Definitions.Def_OAI_Combinatorics_MatchingPSD_TensorBounds
import Definitions.Def_OAI_Combinatorics_MatchingPSD_TypeProbabilities
import Definitions.Def_OAI_Combinatorics_MatchingPSD_TableMoments
import Definitions.Def_OAI_Combinatorics_MatchingPSD_IncidenceKernels
import Definitions.Def_OAI_Combinatorics_MatchingPSD_MatchingIncidence
import Definitions.Def_OAI_Combinatorics_MatchingPSD_SpectralContraction

open OAI OAI.MatchingSmoothing
universe u_1 u_2
open scoped RealInnerProductSpace
variable {E : Type u_1} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem OAI.MatchingSmoothing.trace_square_compression_le (A : Module.End ℝ E) (hA : A.IsSymmetric)
    (W : Submodule ℝ E) :
    LinearMap.trace ℝ W (compression A W * compression A W) ≤
      LinearMap.trace ℝ E (A * A) := by sorry
