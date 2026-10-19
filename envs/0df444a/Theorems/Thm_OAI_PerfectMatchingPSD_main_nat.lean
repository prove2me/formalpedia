-- Prove2me | Theorems.Thm_OAI_PerfectMatchingPSD_main_nat
-- name    : OAI.PerfectMatchingPSD.main_nat
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T05:35:06.932385+00:00
-- url     : https://prove2.me/theorems/ff01eb9c-e8b0-40ae-ab6b-9cfe120ae717
-- title:
--   The PSD rank of the perfect matching slack matrix eventually exceeds $n^p$ for every natural $p$
-- statement:
--   Fix $n\in\mathbb{N}$ and the vertex set $[n]=\{0,1,\dots,n-1\}$. An *edge* is a pair $(a,b)$ of vertices with $a<b$ (so the edges are those of the complete graph $K_n$), and a *perfect matching* is a set $M$ of edges such that every vertex lies in exactly one edge of $M$; write $\mathcal{M}_n$ for the set of perfect matchings. For $U\subseteq[n]$ and $M\in\mathcal{M}_n$ let $\delta_M(U)$ be the number of edges of $M$ with exactly one endpoint in $U$. The slack matrix $S_n$ has its rows indexed by all edges $e$ together with all subsets $U\subseteq[n]$ of odd cardinality, its columns indexed by $\mathcal{M}_n$, and entries
--
--   $$
--   S_n(e,M)=\begin{cases}1, & e\in M,\\ 0, & e\notin M,\end{cases}\qquad\qquad S_n(U,M)=\delta_M(U)-1 .
--   $$
--
--   A *PSD factorization of order $r$* of $S_n$ consists of real symmetric positive semidefinite $r\times r$ matrices $A_i$, one for each row $i$, and $B_M$, one for each $M\in\mathcal{M}_n$ (no equivariance or rank restriction), such that $S_n(i,M)=\operatorname{tr}(A_iB_M)$ for every row $i$ and every $M$. The *PSD rank* $\operatorname{rk}_{\mathrm{psd}}(n)$ is the least integer $r\ge1$ for which $S_n$ has a PSD factorization of order $r$.
--
--   **Theorem.** For every natural number $p$ there is a natural number $n_0\ge4$ such that
--
--   $$
--   n^p<\operatorname{rk}_{\mathrm{psd}}(n)\qquad\text{for every even integer } n\ge n_0 .
--   $$
--
--   The rows of $S_n$ are the slacks of the inequalities $x_e\ge0$ and $\sum_{e\text{ crossing }U}x_e\ge1$ evaluated at the incidence vectors of perfect matchings, so $S_n$ is a slack matrix of the perfect matching polytope of $K_n$. The theorem says that its PSD rank, the quantity that governs the size of semidefinite extended formulations (spectrahedral lifts) of this polytope, eventually exceeds every fixed polynomial in $n$, uniformly over all even $n$ beyond a threshold. This is the integer-exponent form of the main result; the version with an arbitrary real exponent $C>0$ follows by rounding $C$ up to an integer.
--
--   **Formalization Note** The PSD rank is `psdRank n = sInf {r : ℕ | 0 < r ∧ HasFactorization n r}`; by the Lean convention `sInf ∅ = 0` it would be $0$ if no factorization of positive order existed, and the statement does not presuppose that one exists. `Matrix.PosSemidef` for real matrices includes symmetry. Vertices are `Fin n`, rows form the sum type `Edge n ⊕ OddCut n`, and odd sets of every odd size (including singletons and complements of singletons) are rows. The inequality is between real numbers, with $n^p$ the natural-number power of the cast of $n$; $p=0$ is allowed, in which case the claim reads $1<\operatorname{rk}_{\mathrm{psd}}(n)$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/MatchingPSD/Main.lean#L9-L51

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
import Definitions.Def_OAI_Combinatorics_MatchingPSD_Parameters

open OAI OAI.PerfectMatchingPSD
open MatchingSmoothing MatchingInterpolation Matrix Filter Asymptotics
open scoped BigOperators MatrixOrder

theorem OAI.PerfectMatchingPSD.main_nat (p : ℕ) : ∃ n₀ : ℕ, 4 ≤ n₀ ∧
    ∀ n : ℕ, n₀ ≤ n → Even n → (n:ℝ)^p < (psdRank n:ℝ) := by sorry
