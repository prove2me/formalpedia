-- Prove2me | Theorems.Thm_OAI_PerfectMatchingPSD_slackAffine_vertex
-- name    : OAI.PerfectMatchingPSD.slackAffine_vertex
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T14:24:29.573446+00:00
-- url     : https://prove2.me/theorems/cf81248b-cfa4-4837-9913-ee3465b23752
-- title:
--   The affine slack functions evaluate to the slacks at matching vertices
-- statement:
--   For an even $n$, an edge is a pair $(u,v)$ of vertices of $\{0,\dots,n-1\}$ with $u<v$, and a perfect matching is a set of edges covering every vertex exactly once. The rows of the slack matrix are the edges $e$ and the odd cuts $U\subseteq\{0,\dots,n-1\}$ with $|U|$ odd. The slack of a matching $M$ is $[e\in M]$ for an edge row and $|\{e\in M:e\text{ crosses }U\}|-1$ for an odd-cut row. Let $\sigma_i$ be the affine slack function of row $i$: $\sigma_e(x)=x_e$ and $\sigma_U(x)=\sum_{e\text{ crosses }U}x_e-1$. Let $\chi^M$ be the indicator vector of the perfect matching $M$. Then
--   $$
--   \sigma_i(\chi^M)=\operatorname{slack}(i,M).
--   $$
--
--   So the slack matrix is the matrix of the facet-defining affine functions evaluated at the vertices. This lets the affine geometry of a lift be compared with the combinatorial slack matrix.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/MatchingPSD/AffineSlacks.lean#L19-L38

import Mathlib
import Definitions.Def_MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_PSDEvaluation
import Definitions.Def_OAI_Combinatorics_MatchingPSD_Model
import Definitions.Def_OAI_Combinatorics_MatchingPSD_EdgeProducts__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_Pairings__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_RepresentationDimension__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_ColoringCounts__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_TransitionMatrices__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_TensorBounds__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_TypeProbabilities__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_TableMoments__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_IncidenceKernels__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_MatchingIncidence__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_SpectralContraction__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_EquivariantCompression__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_PolynomialSpaces__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_FiberAverages__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_ScalarSmoothing__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_EdgeMonomials__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_PartialColorings__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_TableCoordinates__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_TablePolynomials__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_PermutationSmoothing__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_MatchingFibers__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_GlobalGeometry__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_AdmissibleTables__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_CutGeometry__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_CellAverages__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_SequentialTests__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_MatrixAverages__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_PolynomialInterpolation__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_MatrixInterpolation__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_GoodCells__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_CellDecoder__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_AffineSlacks

open OAI OAI.PerfectMatchingPSD
open MatchingSmoothing Finset Matrix
open scoped BigOperators

theorem OAI.PerfectMatchingPSD.slackAffine_vertex {n : ℕ} (i : Row n) (M : PerfectMatching n) :
    slackAffine i (matchingPoint M) = slack i M := by sorry
