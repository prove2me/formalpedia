-- Prove2me | Theorems.Thm_OAI_MatchingInterpolation_cell_decoder
-- name    : OAI.MatchingInterpolation.cell_decoder
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T05:28:40.20062+00:00
-- url     : https://prove2.me/theorems/4bd07c05-88d1-4b69-85f9-3508ad24980d
-- title:
--   Cell decoder: polynomially approximable cell matrices force the factorization order to be at least $2^{q-1}$
-- statement:
--   **Perfect matchings.** For a finite set $V$, a perfect matching of $V$ is a permutation $M$ of $V$ with $M(M(v))=v$ and $M(v)\neq v$ for every $v$; its edges are the pairs $\{v,M(v)\}$. Write $\Pi(V)$ for the set of perfect matchings of $V$. A permutation $a$ of $V$ acts on $\Pi(V)$ by relabelling, $a\cdot M=aMa^{-1}$, which sends every edge $\{u,v\}$ of $M$ to $\{a(u),a(v)\}$.
--
--   **The cell vertex set.** For $s,q\in\mathbb{N}$ let $G_{s,q}=A\sqcup B\sqcup C_1\sqcup\dots\sqcup C_q$, where $|A|=|B|=2s+1$ and each cell $C_i$ is a copy of $C=\{1,\dots,s\}\times\{0,1\}$, so $|C_i|=2s$. The local vertex set is $T_s=A\sqcup B\sqcup C$, with $2(3s+1)$ elements. The cross vector of a local matching $N\in\Pi(T_s)$ is $\chi(N)=(\chi_0,\chi_1,\chi_2)\in\mathbb{R}^3$, where $\chi_0$, $\chi_1$ and $\chi_2$ are the numbers of edges of $N$ between $A$ and $B$, between $A$ and $C$, and between $B$ and $C$, respectively.
--
--   **Cuts.** For $y\in\{0,1\}^q$ let $U_y=A\cup\bigcup_{i:\,y_i=1}C_i\subseteq G_{s,q}$, a set of odd size $2s+1+2s\,|\{i:y_i=1\}|$, and for $M\in\Pi(G_{s,q})$ let $\kappa_y(M)$ be the number of edges of $M$ with exactly one endpoint in $U_y$.
--
--   **Cell matrices.** For a cell index $i$, a local matching $N\in\Pi(T_s)$ and matchings $N_j\in\Pi(C)$ for $j\neq i$, let $\mathrm{ext}_i(N,(N_j)_{j\neq i})\in\Pi(G_{s,q})$ be the matching that acts as $N$ on $A\sqcup B\sqcup C_i$ (with $C$ identified with $C_i$) and as $N_j$ inside every other cell $C_j$. For a function $F:\Pi(G_{s,q})\to\mathbb{R}^{r\times r}$ and $x\in\mathbb{R}^3$, the $i$-th cell matrix of $F$ at $x$ is the iterated uniform average
--   $$\mathcal C_i[F](x)=\mathop{\mathbb{E}}_{N\in\Pi(T_s):\ \chi(N)=x}\ \ \mathop{\mathbb{E}}_{(N_j)_{j\neq i}\in\Pi(C)^{q-1}}F\big(\mathrm{ext}_i(N,(N_j)_{j\neq i})\big),$$
--   in which the inner average is over independent choices of the $N_j$ and an average over an empty set is $0$.
--
--   **Polynomials and weights.** $\mathcal P_d$ denotes the real vector space of functions $\mathbb{R}^3\to\mathbb{R}$ spanned by all products of at most $d$ coordinate functions $x\mapsto x_a$, $a\in\{0,1,2\}$ (repetitions allowed, the empty product being the constant $1$); these are exactly the polynomial functions of total degree at most $d$ in three variables. For $k\in\{0,\dots,d\}$ let $\ell_k(\tau)=\prod_{j\in\{0,\dots,d\},\,j\neq k}\frac{\tau-j}{k-j}$ be the Lagrange basis polynomial of the nodes $0,1,\dots,d$, and for $g\in\{0,\dots,d\}^3$ and $v\in\mathbb{R}^3$ let $\Lambda_{g,v}(\tau)=\prod_{a=0}^{2}\ell_{g_a}(v_a\tau)$. With $\alpha=(0,2,0)$, $\beta=(0,0,2)$, $\sigma=(2,0,0)$ and $\pi=(-1,1,1)$ put $w_{d,L}(g)=\big(\Lambda_{g,\alpha}+\Lambda_{g,\beta}-\Lambda_{g,\sigma}-2\Lambda_{g,\pi}+\Lambda_{g,0}\big)(1/L)$, and let $W_{d,L}=\sum_{g\in\{0,\dots,d\}^3}|w_{d,L}(g)|$ be the weight mass.
--
--   **Sample points.** The sample index set is $S_d=\{1,\dots,5\}\sqcup\{0,\dots,d\}^3$, of size $5+(d+1)^3$. For $L\in\mathbb{R}$ the sample points are the five special points $y_1=(1,0,0)$, $y_2=(0,1,1)$, $y_3=(3,0,0)$, $y_4=(1,2,0)$, $y_5=(1,0,2)$ and the grid points $y_g=(1+Lg_0,\,Lg_1,\,Lg_2)$ for $g=(g_0,g_1,g_2)\in\{0,\dots,d\}^3$.
--
--   **Theorem.** Let $s,q,l,r,d\in\mathbb{N}$ with $s\ge1$, $q\ge1$, $l\ge1$ and $2ld\le s$. Let $Q_y$ ($y\in\{0,1\}^q$) and $B_M$ ($M\in\Pi(G_{s,q})$) be positive semidefinite real $r\times r$ matrices with $\operatorname{tr}(Q_yB_M)=\kappa_y(M)-1$ for all $y$ and $M$. Let $P_{i,u,v}\in\mathcal P_d$ for every cell $i$ and $u,v\in\{1,\dots,r\}$, and let $\eta\ge0$, $\delta>0$ and $m\in\mathbb{R}$ satisfy $\operatorname{tr}Q_y\le m$ for all $y$ and
--   $$\big|\mathcal C_i[B](y_t)_{uv}-P_{i,u,v}(y_t)\big|\le\eta\quad\text{for all } i,u,v \text{ and all } t\in S_d,$$
--   with the sample points taken for $L=2l$. Put $W=W_{d,2l}$ and $\varepsilon=q\big(W\cdot2d\cdot2l+r\,(6+W)\,\eta\,m\big)+\delta m$. If $\varepsilon\ge0$ and $q\sqrt{\varepsilon}\le\frac14$, then
--   $$r\ge\frac{2^q}{2}.$$
--
--   The identity $\operatorname{tr}(Q_yB_M)=\kappa_y(M)-1$ says that $(Q_y,B_M)$ is a PSD factorization of order $r$ of the odd-cut slacks of the perfect matchings of $G_{s,q}$ for the $2^q$ cuts $U_y$. The lemma shows that such a factorization cannot have small order if its cell-averaged factors are uniformly close to low-degree polynomials at the sample points; the approximation itself is supplied, after a relabelling, by the good-cell polynomial theorem.
--
--   **Formalization Note** $\kappa_y(M)$ is `tableCoordinate (globalCutColor y) (true,false) M`, which counts the vertices of $U_y$ whose partner lies outside $U_y$. $G_{s,q}$ is `GlobalVertices s q`, $\mathcal C_i[B]$ is `cellMatrix i B`, $y_t$ is `samplePoint d (2*l) t` and $W_{d,L}$ is `weightMass d L`; bits are `Bool` with $1$ = `true`, and cells and matrix indices are 0-based.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/MatchingPSD/CellDecoder.lean#L53-L109

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
attribute [local instance] Classical.propDecidable

theorem OAI.MatchingInterpolation.cell_decoder {s q l r d : ℕ} (hs : 1 ≤ s) (hq : 1 ≤ q) (hsl : 2*l*d ≤ s)
    (Q : (Fin q → Bool) → Matrix (Fin r) (Fin r) ℝ)
    (B : Pairing (GlobalVertices s q) → Matrix (Fin r) (Fin r) ℝ)
    (hQ : ∀ y, (Q y).PosSemidef) (hB : ∀ M, (B M).PosSemidef)
    (hpair : ∀ y M, (Q y*B M).trace = tableCoordinate (globalCutColor y) (true,false) M-1)
    (P : Fin q → Fin r → Fin r → Point → ℝ)
    (hP : ∀ i u v, P i u v ∈ lowDegree coord d)
    {η m δ : ℝ} (hη : 0 ≤ η) (hδ : 0 < δ) (hl : 0 < l)
    (hm : ∀ y, (Q y).trace ≤ m)
    (happrox : ∀ i u v t, |cellMatrix i B (samplePoint d (2*l) t) u v-
      P i u v (samplePoint d (2*l) t)| ≤ η)
    (hε : 0 ≤ (q:ℝ)*(weightMass d (2*l)*(2*d*(2*l))+
      (r:ℝ)*(6+weightMass d (2*l))*η*m)+δ*m)
    (hsmall : (q:ℝ)*Real.sqrt ((q:ℝ)*(weightMass d (2*l)*(2*d*(2*l))+
      (r:ℝ)*(6+weightMass d (2*l))*η*m)+δ*m) ≤ 1/4) :
    (2:ℝ)^q/2 ≤ r := by sorry
