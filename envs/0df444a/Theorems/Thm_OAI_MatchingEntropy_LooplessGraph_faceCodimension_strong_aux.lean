-- Prove2me | Theorems.Thm_OAI_MatchingEntropy_LooplessGraph_faceCodimension_strong_aux
-- name    : OAI.MatchingEntropy.LooplessGraph.faceCodimension_strong_aux
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T01:17:47.242983+00:00
-- url     : https://prove2.me/theorems/7f55a635-bb93-4060-bbcc-b5401ecd63a9
-- title:
--   Active-face codimension in the odd-cut polytope is at most $2(n-2)$
-- statement:
--   Let $G$ be a finite loopless multigraph with vertex set $V$ and edge set $E$: every edge $e\in E$ has two distinct endpoints, and parallel edges are allowed (they are distinct elements of $E$). For $x\in\mathbb{R}^E$, a vertex $v$ and a set $S\subseteq V$ write $\deg_x(v)=\sum_{e\ni v}x_e$ for the weighted degree and $x(\delta(S))=\sum_{e\in\delta(S)}x_e$ for the cut mass, where $\delta(S)$ is the set of edges with exactly one endpoint in $S$. The degree and odd-cut polytope is
--
--   $$
--   Q(G)=\Bigl\{x\in\mathbb{R}^E:\ x_e\ge 0\ \text{for all } e,\ \ \deg_x(v)=1\ \text{for all } v,\ \ x(\delta(S))\ge 1\ \text{for all } S\subseteq V \text{ with } |S| \text{ odd}\Bigr\}.
--   $$
--
--   For $x\in Q(G)$, let $E_+=\{e\in E: x_e>0\}$ be the positive support of $x$, and for $u\in\mathbb{R}^{E_+}$ let $\tilde u\in\mathbb{R}^E$ be its extension by zero. The active face space of $x$ is the linear subspace
--
--   $$
--   \mathcal{F}(G,x)=\Bigl\{u\in\mathbb{R}^{E_+}:\ \deg_{\tilde u}(v)=0\ \text{for all } v\in V,\ \ \tilde u(\delta(T))=0\ \text{for every odd } T\subseteq V \text{ with } x(\delta(T))=1\Bigr\},
--   $$
--
--   the directions supported on $E_+$ that keep every active (tight) constraint of $Q(G)$ at $x$. The face codimension of $x$ is
--
--   $$
--   \operatorname{codim}(G,x)=\dim_{\mathbb{R}}\bigl(\mathbb{R}^{E_+}/\mathcal{F}(G,x)\bigr)=|E_+|-\dim\mathcal{F}(G,x).
--   $$
--
--   **Theorem.** For every natural number $n$, every such multigraph $G$ with $|V|=n$, $n$ even and $n\ge 4$, and every $x\in Q(G)$,
--
--   $$
--   \operatorname{codim}(G,x)\le 2(n-2).
--   $$
--
--   The face codimension is the number of linearly independent active constraints seen on the support of $x$. The theorem bounds it linearly in the number of vertices, independently of the number of edges and of the possibly exponential number of odd cuts. Together with the elementary bound $\operatorname{codim}(G,x)\le|V|$ for graphs with fewer than four vertices, it gives $|E_+|-\dim\mathcal{F}(G,x)\le 2|V|$ at every point of the perfect matching polytope, which is how the support size of a marginal is compared with the rank of a covariance matrix in the matching-entropy argument.
--
--   **Formalization Note** As in Edmonds' theorem, $n$ is quantified before the vertex and edge types to allow strong induction on $n$. The codimension is `Module.finrank` of the quotient module, a natural number, and $2(n-2)$ is computed in $\mathbb{N}$, which is harmless since $n\ge 4$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/PerfectMatching/Face.lean#L191-L234

import Mathlib
import Definitions.Def_MatchingEntropy
import Definitions.Def_OAI_Combinatorics_PerfectMatching_Model
import Definitions.Def_OAI_Combinatorics_PerfectMatching_Basic
import Definitions.Def_OAI_Combinatorics_PerfectMatching_Duality
import Definitions.Def_OAI_Combinatorics_PerfectMatching_Calculus
import Definitions.Def_OAI_Combinatorics_PerfectMatching_SecondVariation
import Definitions.Def_OAI_Combinatorics_PerfectMatching_OddCuts
import Definitions.Def_OAI_Combinatorics_PerfectMatching_Coupling
import Definitions.Def_OAI_Combinatorics_PerfectMatching_Contraction
import Definitions.Def_OAI_Combinatorics_PerfectMatching_Polytope
import Definitions.Def_OAI_Combinatorics_PerfectMatching_Face

open OAI OAI.MatchingEntropy OAI.MatchingEntropy.LooplessGraph
open scoped BigOperators Topology
open Filter
variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

theorem OAI.MatchingEntropy.LooplessGraph.faceCodimension_strong_aux (n : ℕ) :
    ∀ {W F : Type*} [Fintype W] [Fintype F] [DecidableEq W] [DecidableEq F]
      (G : LooplessGraph W F), Fintype.card W=n → Even n → 4≤n →
      ∀ x ∈ G.constraintPolytope, G.faceCodimension x ≤ 2*(n-2) := by sorry
