-- Prove2me | Theorems.Thm_OAI_MatchingInterpolation_conditional_cell_lower_bound
-- name    : OAI.MatchingInterpolation.conditional_cell_lower_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T05:29:47.599571+00:00
-- url     : https://prove2.me/theorems/e80c3249-b4c4-4e21-b913-16388ac9c3c1
-- title:
--   Conditional exponential lower bound for normalised PSD factorizations of relabelled odd-cut slacks
-- statement:
--   **Perfect matchings.** For a finite set $V$, a perfect matching of $V$ is a permutation $M$ of $V$ with $M(M(v))=v$ and $M(v)\neq v$ for every $v$; its edges are the pairs $\{v,M(v)\}$. Write $\Pi(V)$ for the set of perfect matchings of $V$. A permutation $a$ of $V$ acts on $\Pi(V)$ by relabelling, $a\cdot M=aMa^{-1}$, which sends every edge $\{u,v\}$ of $M$ to $\{a(u),a(v)\}$.
--
--   **The cell vertex set.** For $s,q\in\mathbb{N}$ let $G_{s,q}=A\sqcup B\sqcup C_1\sqcup\dots\sqcup C_q$, where $|A|=|B|=2s+1$ and each cell $C_i$ is a copy of $C=\{1,\dots,s\}\times\{0,1\}$, so $|C_i|=2s$.
--
--   **Cuts.** For $y\in\{0,1\}^q$ let $U_y=A\cup\bigcup_{i:\,y_i=1}C_i\subseteq G_{s,q}$, a set of odd size $2s+1+2s\,|\{i:y_i=1\}|$, and for $M\in\Pi(G_{s,q})$ let $\kappa_y(M)$ be the number of edges of $M$ with exactly one endpoint in $U_y$.
--
--   **Theorem.** For every $K\in\mathbb{N}$ there exist $d,H\in\mathbb{N}$ with $d\ge1$ and a real $D>0$ such that the following holds. Let $s,q,l,r\in\mathbb{N}$ with $H\le3s+1$, $s\ge1$, $q\ge1$, $l\ge1$, $r\ge1$ and $2ld\le s$, and let $m>0$ be real. Let $Q_{a,y}$, for permutations $a$ of $G_{s,q}$ and $y\in\{0,1\}^q$, and $B_M$, for $M\in\Pi(G_{s,q})$, be positive semidefinite real $r\times r$ matrices such that for all $a$, $y$ and $M$
--   $$\operatorname{tr}Q_{a,y}\le m,\qquad\operatorname{tr}B_M\le r,\qquad\operatorname{tr}\big(Q_{a,y}B_{a\cdot M}\big)=\kappa_y(M)-1.$$
--   If moreover
--   $$\frac{q\,r^4\,\big(5+(d+1)^3\big)}{\big(2(3s+1)\big)^{2K}}\le\Big(\frac{1}{r\,m\cdot2l}\Big)^2\qquad\text{and}\qquad16\,q^2\,(qD+1)\le2l,$$
--   then $r\ge2^q/2$.
--
--   This packages the cell-averaging machinery into a statement about factorizations alone: a PSD factorization of order $r$ with normalised traces that reproduces the odd-cut slacks $\kappa_y(M)-1$ for all relabelled cuts must have order at least $2^{q-1}$, provided the numerical conditions hold. In the main argument it is applied with $K=10(p+1)$, $q=t$, $s=4(d+1)t^4$, $l=t^4$ and $m=n+1$, where the factors come from a hypothetical PSD factorization of the perfect matching slack matrix on $n$ vertices of order at most $n^p$, which leads to a contradiction for large even $n$.
--
--   **Formalization Note** Permutations are `Equiv.Perm (GlobalVertices s q)`, $a\cdot M$ is `Pairing.relabel a M`, $\kappa_y(M)$ is `tableCoordinate (globalCutColor y) (true,false) M`, and $5+(d+1)^3$ appears as `Fintype.card (SampleIndex d)`. Bits are `Bool` with $1$ = `true`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/MatchingPSD/CellLowerBound.lean#L42-L87

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

open OAI OAI.MatchingInterpolation
open MatchingSmoothing PerfectMatchingPSD Matrix
open scoped BigOperators MatrixOrder

theorem OAI.MatchingInterpolation.conditional_cell_lower_bound (K : ℕ) :
    ∃ d H : ℕ, 0 < d ∧ ∃ D : ℝ, 0 < D ∧
    ∀ s q l r : ℕ, H ≤ 3*s+1 → 1 ≤ s → 1 ≤ q → 2*l*d ≤ s → 1 ≤ l → 0 < r →
    ∀ m : ℝ, 0 < m →
    ∀ (Q : Equiv.Perm (GlobalVertices s q) → (Fin q → Bool) → Matrix (Fin r) (Fin r) ℝ)
      (B : Pairing (GlobalVertices s q) → Matrix (Fin r) (Fin r) ℝ),
      (∀ a y, (Q a y).PosSemidef) → (∀ M, (B M).PosSemidef) →
      (∀ a y, (Q a y).trace ≤ m) → (∀ M, (B M).trace ≤ (r:ℝ)) →
      (∀ a y M, (Q a y*B (Pairing.relabel a M)).trace =
        tableCoordinate (globalCutColor y) (true,false) M-1) →
      (q:ℝ)*r^4*(Fintype.card (SampleIndex d))*((2*(3*s+1):ℝ)^(2*K))⁻¹ ≤
        (1/((r:ℝ)*m*(2*l)))^2 →
      16*(q:ℝ)^2*((q:ℝ)*D+1) ≤ 2*l →
      (2:ℝ)^q/2 ≤ r := by sorry
