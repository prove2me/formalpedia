-- Prove2me | Theorems.Thm_OAI_DiscreteFree_PortGraph_Matched_exists_based
-- name    : OAI.DiscreteFree.PortGraph.Matched.exists_based
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T09:57:21.348933+00:00
-- url     : https://prove2.me/theorems/75cd1631-2d7d-4977-afb6-96ccbc4fdbae
-- title:
--   A matched walk in a port graph yields an explicit compatible path of states
-- statement:
--   A *port graph* consists of a set $X$ of vertices, a set $D$ of ports with an involution $e\mapsto\bar e$, and a move map $X\times D\to X$, $(x,e)\mapsto x\cdot e$, such that $(x\cdot e)\cdot\bar e=x$ for all $x$ and $e$. For a word $w=e_1e_2\cdots e_n$ over $D$ and $0\le i\le n$ write $x\cdot w_{\le i}=(\cdots((x\cdot e_1)\cdot e_2)\cdots)\cdot e_i$ for the vertex reached after the first $i$ steps of the walk from $x$ along $w$ (so $x\cdot w_{\le 0}=x$).
--
--   Let $S$ be a set of *states*, $\kappa\subseteq X\times S$ a *compatibility* relation and $\tau\subseteq S\times S$ a *transition* relation. The walk from $x$ along $w$ is *matched from the state $j$*, written $\mathrm{Matched}(x,j,w)$, according to the recursive definition: $\mathrm{Matched}(x,j,\varnothing)$ means $\kappa(x,j)$, and $\mathrm{Matched}(x,j,e\,w')$ means that $\kappa(x,j)$ holds and there is a state $k$ with $\tau(j,k)$ and $\mathrm{Matched}(x\cdot e,k,w')$.
--
--   **Theorem.** If $\mathrm{Matched}(x,j,w)$ holds for a word $w=e_1\cdots e_n$, then there are states $j_0,j_1,\dots,j_n\in S$ with $j_0=j$ and $\tau(j_{i-1},j_i)$ for $1\le i\le n$, such that
--   $$
--   \kappa\bigl(x\cdot w_{\le i},\,j_i\bigr)\qquad\text{for every }0\le i\le n .
--   $$
--
--   The recursive notion of a matched walk is thereby converted into an explicit path of $n$ transitions in the state space that shadows the walk step by step. Paths of states can be counted (there are at most $|S|\,Q^n$ of them when every state has at most $Q$ successors), and this is how one bounds the number of vertices of a large random graph from which some matched walk starts.
--
--   **Formalization Note** No finiteness is assumed. The state path is an element `p` of `StatePaths.Based trans j n`, the type of sequences of $n$ transition choices starting at $j$, and its $i$-th state is `StatePaths.vertex trans j p i` for `i : Fin (n+1)`; the vertex $x\cdot w_{\le i}$ is `G.walk x (w.take i)`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/LipschitzFree/GraphWalks.lean#L112-L128

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

open OAI OAI.DiscreteFree OAI.DiscreteFree.PortGraph
open scoped BigOperators ENNReal
open scoped Classical
variable {X D S : Type*} (G : PortGraph X D)
    (compatible : X → S → Prop) (trans : S → S → Prop)

theorem OAI.DiscreteFree.PortGraph.Matched.exists_based {x : X} {j : S} {w : List D}
    (h : G.Matched compatible trans x j w) :
    ∃ p : StatePaths.Based trans j w.length, ∀ i : Fin (w.length+1),
      compatible (G.walk x (w.take i.val)) (StatePaths.vertex trans j p i) := by sorry
