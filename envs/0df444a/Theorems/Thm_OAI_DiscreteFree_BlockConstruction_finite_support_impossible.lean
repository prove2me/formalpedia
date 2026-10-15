-- Prove2me | Theorems.Thm_OAI_DiscreteFree_BlockConstruction_finite_support_impossible
-- name    : OAI.DiscreteFree.BlockConstruction.finite_support_impossible
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-15T10:14:40.929256+00:00
-- url     : https://prove2.me/theorems/08d04ec3-19aa-4c8b-8f90-c6f14de7898b
-- title:
--   No finite-support operator of norm at most $2p$ almost fixes every anchor of the metric block $M_p$
-- statement:
--   *Free spaces.* For a pointed metric space $(M,o)$, $\mathrm{Lip}_0(M)$ is the space of Lipschitz functions $f\colon M\to\mathbb R$ with $f(o)=0$, normed by the best Lipschitz constant. The *Lipschitz-free space* $\mathcal F(M)$ is the closed linear span, in the dual $\mathrm{Lip}_0(M)^*$, of the point evaluations $\delta_x\colon f\mapsto f(x)$ for $x\in M$. Thus $\delta_o=0$ and $\|\delta_x-\delta_y\|=d(x,y)$.
--
--   *Support projections.* Suppose distinct points of $M$ are at distance at least $1$. For $j\in M$, let $\mathbf 1_j$ be the function equal to $1$ at $j$ and $0$ elsewhere, with the convention $\mathbf 1_o=0$; it lies in the unit ball of $\mathrm{Lip}_0(M)$. Let $c_j(u)=u(\mathbf 1_j)$ be the corresponding coordinate functional on $\mathcal F(M)$, so $c_j(\delta_x)=1$ if $x=j\ne o$ and $c_j(\delta_x)=0$ otherwise. For a finite set $S\subseteq M$ the *support projection* is
--   $$
--   P_Su=\sum_{j\in S}c_j(u)\,\delta_j .
--   $$
--   It is a bounded linear projection of $\mathcal F(M)$ onto $\mathrm{span}\{\delta_j:j\in S\}$.
--
--   *The metric block $M_p$.* Fix an integer $p\ge1$ and set $L=10p$, $R=3L$, $K=10p(R+1)$, $D=K+2L+5$, $B=4R+D$, $V=1+4pB$, $g=20V+2$, $\Delta=2g$, $Q=\Delta^{2L+1}$, $H=\Delta^{D+1}$ and $k=2\Delta QH+1$. Let $A=\{0,\dots,g-1\}$ be the generators and $C=\{0,\dots,k-1\}$ the colors.
--
--   - For $N\in\mathbb N$, $B_N$ is the ball of radius $N$ in the free group $F(A)$, $G_N=\mathrm{Sym}(B_N)$, and $\rho_N\colon F(A)\to G_N$ is a fixed homomorphism with $\rho_N(a)h=ah$ whenever $|ah|\le N$.
--   - The vertex set $\mathcal V$ consists of the triples $(N,c,x)$ with $N\in\mathbb N$, $x\in G_N$ and $c\colon G_N\to C$. The $\Delta$ ports $(a,\pm)$ move $(N,c,x)$ to $(N,c,x\,\rho_N(a^{\pm1}))$, and the color of $(N,c,x)$ is $c(x)$.
--   - For a vertex $x$ and a color $i$, $\ell_i(x)$ is the minimum of $D$ and the graph distance from $x$ to a vertex of color $i$. The *label* of $x$ is $\ell(x)=(\ell_i(x))_{i\in C}\in\{0,\dots,D\}^C$. Labels are compared in the sup-metric $|a-b|_\infty=\max_i|a_i-b_i|$.
--   - The *anchors* form the finite set $\mathcal A_p=\{\ell(x):x\in\mathcal V\}$.
--
--   The points of $M_p$ are the disjoint union $\mathcal V\sqcup\mathcal A_p$. The integer weights are $w(u,u)=0$ and, for $u\ne v$:
--
--   - for vertices $x,y$: $w(x,y)=1$ if a port joins $x$ to $y$, and $w(x,y)=4R+D$ otherwise;
--   - for a vertex $x$ and an anchor $a$: $w(x,a)=w(a,x)=R$ if $\ell(x)=a$, and $4R+D$ otherwise;
--   - for distinct anchors: $w(a,b)=2R+|a-b|_\infty$.
--
--   The metric of $M_p$ is the shortest-chain metric $d(u,v)=\min\sum_i w(z_{i-1},z_i)$, taken over finite chains $u=z_0,z_1,\dots,z_m=v$. It is integer-valued, so distinct points are at distance at least $1$. The base point $o_p\in\mathcal A_p$ is the label of the vertex $(0,c_0,\mathrm{id})$, where $c_0$ is the constant coloring by the color $0$.
--
--   **Theorem.** Let $p\ge1$, let $S\subseteq M_p$ be a finite set with $o_p\in S$, and let $T\colon\mathcal F(M_p)\to\mathcal F(M_p)$ be a bounded linear operator. The following three conditions cannot hold simultaneously:
--
--   $$
--   \|T\|\le2p,\qquad P_S\,T=T,\qquad \|T\delta_a-\delta_a\|<1\ \text{ for every anchor } a\in\mathcal A_p .
--   $$
--
--   Equivalently, if an operator $T$ of norm at most $2p$ satisfies $P_ST=T$ for some finite $S$ containing $o_p$, so that its range lies in the span of the point masses $\delta_j$ with $j\in S$, then $\|T\delta_a-\delta_a\|\ge1$ for some anchor $a$. A perturbation argument replaces any finite-rank operator of norm at most $p$ by an operator of this finite-support form. Combined with that argument, the theorem shows that $\mathcal F(M_p)$ fails the bounded approximation property with constant $p$, uniformly on the finite set of anchors.
--
--   **Formalization Note** The space is `BlockConstruction.Block p`, with base point `base p` and anchor set `anchors p`. $P_S$ is `supportProjection (base p) (separation p) S`, built from the proof that $M_p$ is $1$-separated. The hypothesis $P_ST=T$ is stated pointwise, as $P_S(Tu)=Tu$ for all $u$, and the conclusion is `False`. An instance `Fact (0 < R p)` is needed to equip the point set with its metric; it holds for $p\ge1$. Finite rank of $T$ is not assumed, because it follows from $P_ST=T$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/LipschitzFree/BlockObstruction.lean#L102-L174

import Mathlib
import Definitions.Def_DiscreteLipschitzFree
import Definitions.Def_OAI_Analysis_LipschitzFree_PortGraphs
import Definitions.Def_OAI_Analysis_LipschitzFree_RenormingModel
import Definitions.Def_OAI_Analysis_LipschitzFree_Model
import Definitions.Def_OAI_Analysis_LipschitzFree_Parameters
import Definitions.Def_OAI_Analysis_LipschitzFree_BoxLabels
import Definitions.Def_OAI_Analysis_LipschitzFree_MetricClosure
import Definitions.Def_OAI_Analysis_LipschitzFree_MetricBlock
import Definitions.Def_OAI_Analysis_LipschitzFree_Attachment
import Definitions.Def_OAI_Analysis_LipschitzFree_Words
import Definitions.Def_OAI_Analysis_LipschitzFree_StatePaths
import Definitions.Def_OAI_Analysis_LipschitzFree_SignedTests
import Definitions.Def_OAI_Analysis_LipschitzFree_GraphWalks
import Definitions.Def_OAI_Analysis_LipschitzFree_Evaluation
import Definitions.Def_OAI_Analysis_LipschitzFree_Coordinates
import Definitions.Def_OAI_Analysis_LipschitzFree_AffineWeights
import Definitions.Def_OAI_Analysis_LipschitzFree_LabelBumps
import Definitions.Def_OAI_Analysis_LipschitzFree_ScalarTests
import Definitions.Def_OAI_Analysis_LipschitzFree_FiniteQuotients
import Definitions.Def_OAI_Analysis_LipschitzFree_GraphGirth
import Definitions.Def_OAI_Analysis_LipschitzFree_ColorCounting
import Definitions.Def_OAI_Analysis_LipschitzFree_GraphColoring
import Definitions.Def_OAI_Analysis_LipschitzFree_BlockObstruction

open OAI OAI.DiscreteFree OAI.DiscreteFree.BlockConstruction
open scoped BigOperators ENNReal
open scoped Classical BigOperators
open BlockParameters
variable (p : ℕ) [Fact (0 < R p)]

theorem OAI.DiscreteFree.BlockConstruction.finite_support_impossible (hp : 1 ≤ p) (S : Finset (Block p)) (ho : base p ∈ S)
    (T : FreeSpace (base p) →L[ℝ] FreeSpace (base p))
    (hn : ‖T‖ ≤ 2*(p : ℝ))
    (hfixed : ∀ u, supportProjection (base p) (separation p) S (T u) = T u)
    (he : ∀ a ∈ anchors p, ‖T (delta (base p) a) - delta (base p) a‖ < 1) : False := by sorry
