-- Prove2me | Theorems.Thm_OAI_MatchingInterpolation_good_cell_polynomials
-- name    : OAI.MatchingInterpolation.good_cell_polynomials
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T05:23:01.188499+00:00
-- url     : https://prove2.me/theorems/2051ebd6-9cdb-4c9d-8801-137b1f3d855b
-- title:
--   Uniform low-degree polynomial approximation of cell-averaged PSD factors after a relabelling
-- statement:
--   **Perfect matchings.** For a finite set $V$, a perfect matching of $V$ is a permutation $M$ of $V$ with $M(M(v))=v$ and $M(v)\neq v$ for every $v$; its edges are the pairs $\{v,M(v)\}$. Write $\Pi(V)$ for the set of perfect matchings of $V$. A permutation $a$ of $V$ acts on $\Pi(V)$ by relabelling, $a\cdot M=aMa^{-1}$, which sends every edge $\{u,v\}$ of $M$ to $\{a(u),a(v)\}$.
--
--   **The cell vertex set.** For $s,q\in\mathbb{N}$ let $G_{s,q}=A\sqcup B\sqcup C_1\sqcup\dots\sqcup C_q$, where $|A|=|B|=2s+1$ and each cell $C_i$ is a copy of $C=\{1,\dots,s\}\times\{0,1\}$, so $|C_i|=2s$. The local vertex set is $T_s=A\sqcup B\sqcup C$, with $2(3s+1)$ elements. The cross vector of a local matching $N\in\Pi(T_s)$ is $\chi(N)=(\chi_0,\chi_1,\chi_2)\in\mathbb{R}^3$, where $\chi_0$, $\chi_1$ and $\chi_2$ are the numbers of edges of $N$ between $A$ and $B$, between $A$ and $C$, and between $B$ and $C$, respectively.
--
--   **Cell matrices.** For a cell index $i$, a local matching $N\in\Pi(T_s)$ and matchings $N_j\in\Pi(C)$ for $j\neq i$, let $\mathrm{ext}_i(N,(N_j)_{j\neq i})\in\Pi(G_{s,q})$ be the matching that acts as $N$ on $A\sqcup B\sqcup C_i$ (with $C$ identified with $C_i$) and as $N_j$ inside every other cell $C_j$. For a function $F:\Pi(G_{s,q})\to\mathbb{R}^{r\times r}$ and $x\in\mathbb{R}^3$, the $i$-th cell matrix of $F$ at $x$ is the iterated uniform average
--   $$\mathcal C_i[F](x)=\mathop{\mathbb{E}}_{N\in\Pi(T_s):\ \chi(N)=x}\ \ \mathop{\mathbb{E}}_{(N_j)_{j\neq i}\in\Pi(C)^{q-1}}F\big(\mathrm{ext}_i(N,(N_j)_{j\neq i})\big),$$
--   in which the inner average is over independent choices of the $N_j$ and an average over an empty set is $0$.
--
--   **Polynomials.** $\mathcal P_d$ denotes the real vector space of functions $\mathbb{R}^3\to\mathbb{R}$ spanned by all products of at most $d$ coordinate functions $x\mapsto x_a$, $a\in\{0,1,2\}$ (repetitions allowed, the empty product being the constant $1$); these are exactly the polynomial functions of total degree at most $d$ in three variables.
--
--   **Sample points.** The sample index set is $S_d=\{1,\dots,5\}\sqcup\{0,\dots,d\}^3$, of size $5+(d+1)^3$. For $L\in\mathbb{R}$ the sample points are the five special points $y_1=(1,0,0)$, $y_2=(0,1,1)$, $y_3=(3,0,0)$, $y_4=(1,2,0)$, $y_5=(1,0,2)$ and the grid points $y_g=(1+Lg_0,\,Lg_1,\,Lg_2)$ for $g=(g_0,g_1,g_2)\in\{0,\dots,d\}^3$.
--
--   **Theorem.** For every $K\in\mathbb{N}$ there exist $d,H\in\mathbb{N}$ with $d\ge1$ such that the following holds for all $s,q,l,r\in\mathbb{N}$ with $H\le3s+1$, $s\ge1$ and $2ld\le s$. Let $B:\Pi(G_{s,q})\to\mathbb{R}^{r\times r}$ be such that every $B(M)$ is positive semidefinite with $\operatorname{tr}B(M)\le r$, and let $\eta\ge0$ satisfy
--   $$\frac{q\,r^4\,\big(5+(d+1)^3\big)}{\big(2(3s+1)\big)^{2K}}\le\eta^2.$$
--   Then there exist a permutation $a$ of $G_{s,q}$ and polynomials $P_{i,u,v}\in\mathcal P_d$, one for each cell $i$ and each pair of matrix indices $u,v\in\{1,\dots,r\}$, such that, with $B^a(M)=B(a\cdot M)$ and the sample points taken with $L=2l$,
--   $$\Big|\,\mathcal C_i[B^a](y_t)_{uv}-P_{i,u,v}(y_t)\Big|\le\eta\qquad\text{for all } i,\ u,\ v\ \text{and all } t\in S_d.$$
--
--   Thus, after a single relabelling of the vertex set, every entry of every cell-averaged factor matrix agrees up to $\eta$, at all $5+(d+1)^3$ sample points, with a polynomial of degree at most $d$ in the cross vector; $d$ and $H$ depend only on $K$, and the admissible accuracy improves like $(2(3s+1))^{-K}$. This is the approximation input of the cell decoder, which converts such approximations into the lower bound $r\ge2^{q-1}$ for PSD factorizations of odd-cut slacks.
--
--   **Formalization Note** Matchings are `Pairing V`, the relabelling is `Pairing.relabel a M`, $G_{s,q}$ is `GlobalVertices s q`, $\mathcal C_i$ is `cellMatrix i`, $S_d$ is `SampleIndex d` and $y_t$ is `samplePoint d (2*l) t`. Cells and matrix indices are 0-based (`Fin q`, `Fin r`). Averages are Mathlib's `Finset.expect`, which returns $0$ on an empty set.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/MatchingPSD/GoodCells.lean#L25-L85

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

open OAI OAI.MatchingInterpolation
open MatchingSmoothing PerfectMatchingPSD Matrix
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem OAI.MatchingInterpolation.good_cell_polynomials (K : ℕ) :
    ∃ d H : ℕ, 0 < d ∧ ∀ s q l r : ℕ, H ≤ 3*s+1 → 1 ≤ s → 2*l*d ≤ s →
      ∀ (B : Pairing (GlobalVertices s q) → Matrix (Fin r) (Fin r) ℝ),
      (∀ M, (B M).PosSemidef) → (∀ M, (B M).trace ≤ (r:ℝ)) →
      ∀ η : ℝ, 0 ≤ η →
      (q:ℝ)*r^4*(Fintype.card (SampleIndex d))*((2*(3*s+1):ℝ)^(2*K))⁻¹ ≤ η^2 →
      ∃ a : Equiv.Perm (GlobalVertices s q),
      ∃ P : Fin q → Fin r → Fin r → Point → ℝ,
        (∀ i u v, P i u v ∈ lowDegree coord d) ∧
        ∀ i u v t, |cellMatrix i (fun M => B (Pairing.relabel a M))
          (samplePoint d (2*l) t) u v-P i u v (samplePoint d (2*l) t)| ≤ η := by sorry
