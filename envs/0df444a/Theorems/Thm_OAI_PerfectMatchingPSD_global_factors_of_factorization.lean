-- Prove2me | Theorems.Thm_OAI_PerfectMatchingPSD_global_factors_of_factorization
-- name    : OAI.PerfectMatchingPSD.global_factors_of_factorization
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T05:32:34.317853+00:00
-- url     : https://prove2.me/theorems/69940b30-e67b-4f6b-9a49-4eca26f37463
-- title:
--   From a PSD factorization of the perfect matching slack matrix to normalised odd-cut factors on a padded cell vertex set
-- statement:
--   **Slack matrix.** Let $n\in\mathbb{N}$ and $[n]=\{0,1,\dots,n-1\}$. Edges are pairs $(a,b)\in[n]^2$ with $a<b$, and a perfect matching of $[n]$ is a set of edges such that every vertex lies in exactly one of them. The rows are all edges $e$ and all odd sets $U\subseteq[n]$ ($|U|$ odd). The slack of a row at a perfect matching $M$ is $1$ or $0$ for an edge row $e$, according to whether $e\in M$, and $\operatorname{cross}_U(M)-1$ for an odd-set row $U$, where $\operatorname{cross}_U(M)$ is the number of edges of $M$ with exactly one endpoint in $U$. A PSD factorization of order $r$ consists of positive semidefinite real $r\times r$ matrices $A_i$ for all rows $i$ and $B_M$ for all perfect matchings $M$ such that $\operatorname{slack}(i,M)=\operatorname{tr}(A_iB_M)$ for all $i$ and $M$.
--
--   **Perfect matchings.** For a finite set $V$, a perfect matching of $V$ is a permutation $M$ of $V$ with $M(M(v))=v$ and $M(v)\neq v$ for every $v$; its edges are the pairs $\{v,M(v)\}$. Write $\Pi(V)$ for the set of perfect matchings of $V$. A permutation $a$ of $V$ acts on $\Pi(V)$ by relabelling, $a\cdot M=aMa^{-1}$, which sends every edge $\{u,v\}$ of $M$ to $\{a(u),a(v)\}$. On $[n]$ this involution description is equivalent to the edge-set description above; it is used for the abstract vertex sets below.
--
--   **The cell vertex set.** For $s,q\in\mathbb{N}$ let $G_{s,q}=A\sqcup B\sqcup C_1\sqcup\dots\sqcup C_q$, where $|A|=|B|=2s+1$ and each cell $C_i$ is a copy of $C=\{1,\dots,s\}\times\{0,1\}$, so $|C_i|=2s$.
--
--   **Cuts.** For $y\in\{0,1\}^q$ let $U_y=A\cup\bigcup_{i:\,y_i=1}C_i\subseteq G_{s,q}$, a set of odd size $2s+1+2s\,|\{i:y_i=1\}|$, and for $M\in\Pi(G_{s,q})$ let $\kappa_y(M)$ be the number of edges of $M$ with exactly one endpoint in $U_y$.
--
--   **Theorem.** Let $n\ge1$ be even, let $r,s,q\in\mathbb{N}$, and suppose that the slack matrix on $[n]$ has a PSD factorization of order $r$. Let $W$ be a finite set with a bijection $\epsilon:G_{s,q}\sqcup W\to[n]$, and let $M_W\in\Pi(W)$. Then there exist positive semidefinite real $r\times r$ matrices $Q_{a,y}$, for permutations $a$ of $G_{s,q}$ and $y\in\{0,1\}^q$, and $B_M$, for $M\in\Pi(G_{s,q})$, such that for all $a$, $y$ and $M$
--   $$\operatorname{tr}Q_{a,y}\le n+1,\qquad\operatorname{tr}B_M\le r,\qquad\operatorname{tr}\big(Q_{a,y}B_{a\cdot M}\big)=\kappa_y(M)-1.$$
--
--   This is the reduction from a global PSD factorization to the cell set-up: the cell vertex set is embedded into $[n]$, the remaining vertices $W$ are frozen by the fixed matching $M_W$, and the relabelled cuts $a(U_y)$ become odd-set rows. The output is exactly the factor data required by the conditional cell lower bound, with trace bound $m=n+1$.
--
--   **Formalization Note** The hypothesis is `HasFactorization n r`. A bijection $\epsilon$ exists only when $|G_{s,q}|+|W|=n$, i.e. $2s(q+2)+2+|W|=n$. The set $W$ is a `Type` with a `Fintype` instance, matchings of $G_{s,q}$ and $W$ are `Pairing` objects (fixed-point-free involutions), $a\cdot M$ is `Pairing.relabel a M`, and $\kappa_y(M)$ is `tableCoordinate (globalCutColor y) (true,false) M`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/MatchingPSD/Padding.lean#L59-L88

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
import Definitions.Def_OAI_Combinatorics_MatchingPSD_MatchingConversion
import Definitions.Def_OAI_Combinatorics_MatchingPSD_Padding

open OAI OAI.PerfectMatchingPSD
universe u_1 u_2 u_3 u_4 u_5 u_6 u_7
open MatchingSmoothing Matrix
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem OAI.PerfectMatchingPSD.global_factors_of_factorization {n r s q : ℕ} (hn : Even n) (hnpos : 1 ≤ n)
    (hfac : HasFactorization n r) {W : Type} [Fintype W]
    (e : (GlobalVertices s q ⊕ W) ≃ Fin n) (MW : Pairing W) :
    ∃ (Q : Equiv.Perm (GlobalVertices s q) → (Fin q → Bool) → Matrix (Fin r) (Fin r) ℝ)
      (B : Pairing (GlobalVertices s q) → Matrix (Fin r) (Fin r) ℝ),
      (∀ a y, (Q a y).PosSemidef) ∧ (∀ M, (B M).PosSemidef) ∧
      (∀ a y, (Q a y).trace ≤ (n:ℝ)+1) ∧ (∀ M, (B M).trace ≤ (r:ℝ)) ∧
      ∀ a y M, (Q a y * B (Pairing.relabel a M)).trace =
        tableCoordinate (globalCutColor y) (true,false) M - 1 := by sorry
