-- Prove2me | Theorems.Thm_OAI_PerfectMatchingPSD_cut_degree_identity
-- name    : OAI.PerfectMatchingPSD.cut_degree_identity
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T05:31:35.4447+00:00
-- url     : https://prove2.me/theorems/81f05bd7-dd1a-4ced-b8be-dc23b170a1a6
-- title:
--   Endpoint count of a vertex set in a perfect matching: twice the internal edges plus the crossing edges
-- statement:
--   Let $n\in\mathbb{N}$ and $[n]=\{0,1,\dots,n-1\}$. An edge is a pair $(a,b)\in[n]^2$ with $a<b$, and a perfect matching is a set $M$ of edges such that every vertex of $[n]$ lies in exactly one edge of $M$. An edge $(a,b)$ crosses a set $U\subseteq[n]$ if exactly one of $a$ and $b$ lies in $U$; let $\operatorname{cross}_U(M)$ be the number of edges of $M$ that cross $U$.
--
--   **Theorem.** For every $U\subseteq[n]$ and every perfect matching $M$ of $[n]$,
--   $$|U|=2\,\big|\{(a,b)\in M:\ a\in U\text{ and }b\in U\}\big|+\operatorname{cross}_U(M).$$
--
--   Consequently $\operatorname{cross}_U(M)\le|U|\le n$, and $\operatorname{cross}_U(M)$ has the same parity as $|U|$, so an odd set is crossed by at least one edge of every perfect matching. For the slack matrix of the perfect matching polytope, where the row of an odd set $U$ has slack $\operatorname{cross}_U(M)-1$, this gives the bound $\operatorname{slack}\le n-1$ on odd-set rows, which is used to normalise PSD factorizations.
--
--   **Formalization Note** Edges are the subtype `{p : Fin n × Fin n // p.1 < p.2}`, a perfect matching is a `Finset` of edges whose filter of edges incident to any vertex has cardinality one, and $\operatorname{cross}_U(M)$ is `crossingCount U M`. The identity is an equality of natural numbers.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/MatchingPSD/FiniteFactorization.lean#L38-L51

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
import Definitions.Def_OAI_Combinatorics_MatchingPSD_EquivariantCompression
import Definitions.Def_OAI_Combinatorics_MatchingPSD_PolynomialSpaces
import Definitions.Def_OAI_Combinatorics_MatchingPSD_FiberAverages
import Definitions.Def_OAI_Combinatorics_MatchingPSD_ScalarSmoothing
import Definitions.Def_OAI_Combinatorics_MatchingPSD_EdgeMonomials
import Definitions.Def_OAI_Combinatorics_MatchingPSD_PartialColorings
import Definitions.Def_OAI_Combinatorics_MatchingPSD_TableCoordinates
import Definitions.Def_OAI_Combinatorics_MatchingPSD_TablePolynomials
import Definitions.Def_OAI_Combinatorics_MatchingPSD_PermutationSmoothing
import Definitions.Def_OAI_Combinatorics_MatchingPSD_MatchingFibers
import Definitions.Def_OAI_Combinatorics_MatchingPSD_GlobalGeometry
import Definitions.Def_OAI_Combinatorics_MatchingPSD_AdmissibleTables
import Definitions.Def_OAI_Combinatorics_MatchingPSD_CutGeometry
import Definitions.Def_OAI_Combinatorics_MatchingPSD_CellAverages
import Definitions.Def_OAI_Combinatorics_MatchingPSD_SequentialTests
import Definitions.Def_OAI_Combinatorics_MatchingPSD_MatrixAverages
import Definitions.Def_OAI_Combinatorics_MatchingPSD_PolynomialInterpolation
import Definitions.Def_OAI_Combinatorics_MatchingPSD_MatrixInterpolation
import Definitions.Def_OAI_Combinatorics_MatchingPSD_GoodCells
import Definitions.Def_OAI_Combinatorics_MatchingPSD_CellDecoder

open OAI OAI.PerfectMatchingPSD
universe u_1 u_2

theorem OAI.PerfectMatchingPSD.cut_degree_identity {n : ℕ} (U : Finset (Fin n)) (M : PerfectMatching n) :
    U.card = 2 * (M.1.filter fun e => e.1.1 ∈ U ∧ e.1.2 ∈ U).card +
      crossingCount U M := by sorry
