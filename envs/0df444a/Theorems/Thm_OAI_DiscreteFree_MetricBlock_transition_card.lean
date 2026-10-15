-- Prove2me | Theorems.Thm_OAI_DiscreteFree_MetricBlock_transition_card
-- name    : OAI.DiscreteFree.MetricBlock.transition_card
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-15T10:05:30.60508+00:00
-- url     : https://prove2.me/theorems/9bb31e5f-a32f-4510-8b31-7f3f890b2136
-- title:
--   In a metric block every point has at most as many $2L$-neighbours as there are words of length at most $2L$
-- statement:
--   Let $X$ be a set of vertices and $E$ a finite set of ports carrying a port-graph structure: an involution $e\mapsto\bar e$ of $E$ and a move map $(x,e)\mapsto x\cdot e$ with $(x\cdot e)\cdot\bar e=x$. Call distinct vertices $x,y$ *adjacent* if $y=x\cdot e$ for some port $e$. Let $C$ be a finite set of colours, $\mathrm{col}:X\to C$ a colouring, and $\mathrm{cap},R\in\mathbb{N}$ with $R>0$.
--
--   *Labels.* The label of a vertex $x$ is $\ell(x)\in\{0,1,\dots,\mathrm{cap}\}^C$, where $\ell(x)_i$ is the least $n$ such that either $n=\mathrm{cap}$ or some walk of length $n$ from $x$ ends at a vertex of colour $i$. Labels are compared with the sup-distance $d_\infty(\alpha,\beta)=\max_{i\in C}|\alpha_i-\beta_i|$.
--
--   *The metric block.* Its point set is $M=X\sqcup\ell(X)$: the vertices together with one *anchor* for each label that occurs. Put $w(z,z)=0$ and, for distinct points,
--   - $w(x,y)=1$ if the vertices $x,y$ are adjacent and $w(x,y)=4R+\mathrm{cap}$ otherwise;
--   - $w(x,\alpha)=w(\alpha,x)=R$ if $\ell(x)=\alpha$, and $4R+\mathrm{cap}$ otherwise;
--   - $w(\alpha,\beta)=2R+d_\infty(\alpha,\beta)$ for distinct anchors $\alpha,\beta$.
--
--   The block metric $d$ is the shortest-path metric of $w$: $d(u,v)$ is the minimum of $w(z_0,z_1)+\dots+w(z_{m-1},z_m)$ over all finite chains $u=z_0,z_1,\dots,z_m=v$. It takes integer values and is at least $1$ between distinct points.
--
--   **Theorem.** Let $L\in\mathbb{N}$ with $2L<R$. For every finite set $S\subseteq M$ and every $j\in S$,
--   $$
--   \#\{k\in S:\ d(j,k)\le 2L\}\ \le\ \#\{w\ \text{a word over }E:\ |w|\le 2L\}.
--   $$
--
--   The relation $d(j,k)\le 2L$ is the transition relation between states of $S$ that are used to shadow walks in the graph. The theorem says that every state has at most $Q=\sum_{i=0}^{2L}|E|^i$ successors, a bound independent of $S$; this feeds into the count of state paths of length $n$, of which there are at most $|S|\,Q^n$.
--
--   **Formalization Note** The block is `MetricBlock.Point G color cap R`, whose metric instance requires `Fact (0 < R)`; the transition relation is `MetricBlock.Transition`, i.e. `dist j k ≤ (2*L : ℕ)`, and the words of length at most $2L$ form `BoundedWords E (2*L)`. Both counts are `Fintype.card` of subtypes.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/LipschitzFree/ScalarTests.lean#L41-L57

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

open OAI OAI.DiscreteFree OAI.DiscreteFree.MetricBlock
open scoped BigOperators ENNReal
open scoped Classical
variable {X E C : Type*} [Fintype C] [Fintype E]
    (G : PortGraph X E) (color : X → C) (cap R L K : ℕ) [Fact (0 < R)]

theorem OAI.DiscreteFree.MetricBlock.transition_card (hR : 2*L < R) (S : Finset (Point G color cap R)) (j : S) :
    Fintype.card {k : S // Transition G color cap R L j.val k.val} ≤
      Fintype.card (BoundedWords E (2*L)) := by sorry
