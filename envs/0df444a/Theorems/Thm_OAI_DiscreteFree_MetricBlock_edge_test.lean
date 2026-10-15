-- Prove2me | Theorems.Thm_OAI_DiscreteFree_MetricBlock_edge_test
-- name    : OAI.DiscreteFree.MetricBlock.edge_test
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-15T10:06:09.61663+00:00
-- url     : https://prove2.me/theorems/35f716f3-3caf-4c9d-a1ba-c063c2778687
-- title:
--   Opposing $1$-Lipschitz test function for an edge of a metric block, exact outside the exception sets
-- statement:
--   **Setting.** Let $X$ be a set of vertices and $E$ a set of ports with a port-graph structure: an involution $e\mapsto\bar e$ of $E$ and a move map $(x,e)\mapsto x\cdot e$ with $(x\cdot e)\cdot\bar e=x$. Let $C$ be a finite set of colours, $\mathrm{col}:X\to C$, and $\mathrm{cap},R,L,K\in\mathbb{N}$ with $R>0$. For a vertex $x$ let $\ell(x)\in\{0,\dots,\mathrm{cap}\}^C$ be its label: $\ell(x)_i$ is the least $n$ such that $n=\mathrm{cap}$ or some walk of length $n$ from $x$ ends at a vertex of colour $i$; labels are compared with the sup-distance $d_\infty$. Let $(M,d)$ be the metric block: $M=X\sqcup\ell(X)$ (the vertices and one anchor for each occurring label), and $d$ is the shortest-path metric of the weights $1$ between adjacent vertices, $4R+\mathrm{cap}$ between non-adjacent distinct vertices, $R$ between a vertex and the anchor of its own label, $4R+\mathrm{cap}$ between a vertex and any other anchor, and $2R+d_\infty(\alpha,\beta)$ between distinct anchors $\alpha,\beta$. Let $\lambda:M\to\{0,\dots,\mathrm{cap}\}^C$ be the label map ($\lambda(x)=\ell(x)$ on vertices and $\lambda(\alpha)=\alpha$ on anchors), and for a vertex $x$ let
--   $$b_x(t)=L\cdot\max\Bigl(1-\frac{d_\infty\bigl(\ell(x),\lambda(t)\bigr)}{K},\,0\Bigr),\qquad t\in M,$$
--   be the label bump around $x$.
--
--   **Records and exception sets.** Fix a finite set $S\subseteq M$ of *states* and $n\in\mathbb{N}$. A vertex $x$ is *compatible* with a state $j$ if $d_\infty(\ell(x),\lambda(j))\le K+2L+1$, and there is a *transition* from $j$ to $k$ if $d(j,k)\le 2L$. A word $e_1\cdots e_m$ over $E$ is *reduced* if $e_{i+1}\ne\bar e_i$ for all $i$. The walk from $x$ along $w$ is *matched* from the state $j$ if $x$ is compatible with $j$ and, when $w=e\,w'$ is nonempty, there is a transition from $j$ to some state $k$ such that the walk from $x\cdot e$ along $w'$ is matched from $k$. The vertex $x$ is *$n$-good* if no reduced word of length $n$ has a walk from $x$ that is matched from some state. The *record* $r_n(x,e,j)$ is the largest $t\le n$ such that $t=0$ or some reduced word of length $t$ beginning with $e$ has a walk from $x$ matched from $j$. A state $j$ is *exceptional* for $(x,e)$ if $r_n(x,g,j)<r_n(x,e,j)$ for every port $g\ne e$. Finally, the *exception set* $\mathcal E_n(x,e)\subseteq S$ consists of all states in $S$ if $x$ is not $n$-good, and of the states exceptional for $(x,e)$ if $x$ is $n$-good.
--
--   **Theorem.** Assume $L>0$, $K>0$ and $L\le K$. Let $S\subseteq M$ be finite, $n\in\mathbb{N}$, $x$ a vertex and $e$ a port, and put $x'=x\cdot e$. Then there is a $1$-Lipschitz function $f:M\to\mathbb{R}$ with $|f(z)|\le L$ for all $z\in M$ such that
--   $$
--   f(j)=b_x(j)\ \ \text{for } j\in S\setminus\mathcal E_n(x,e),\qquad f(j)=-\,b_{x'}(j)\ \ \text{for } j\in S\setminus\mathcal E_n(x',\bar e).
--   $$
--
--   This is the test function attached to the oriented edge $(x,e)$. Paired with the affine weights of $T\delta(x)$ and $T\delta(x')$ for an operator $T$ on the Lipschitz-free space of the block, it agrees with the positive bump around $x$ and with the negative bump around $x'$ except on the exception sets. The difference of the two pairings is therefore at least the sum of the two bump masses minus $2L$ times the variation of the weights on the exception sets, while a Lipschitz bound for $T$ caps the same difference from above.
--
--   **Formalization Note** The block is `MetricBlock.Point G color cap R` with `Fact (0 < R)`. Compatibility, transitions and exception sets are `MetricBlock.Compatible`, `MetricBlock.Transition` and `MetricBlock.exceptionSet`; matched walks, goodness and records are `PortGraph.Matched`, `PortGraph.Good` and `PortGraph.record` (a `Nat.findGreatest`), and exceptionality is `Exceptional`. The bumps are `labelBump` composed with the label map, with $L$ and $K$ natural numbers cast to reals. No finiteness of $E$ is needed.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/LipschitzFree/ScalarTests.lean#L117-L157

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

omit [Fintype E] in
theorem OAI.DiscreteFree.MetricBlock.edge_test (hL : 0 < L) (hK : 0 < K) (hLK : L ≤ K)
    (S : Finset (Point G color cap R)) (n : ℕ) (x : X) (e : E) :
    ∃ f : Point G color cap R → ℝ, LipschitzWith 1 f ∧ (∀ z, |f z| ≤ L) ∧
      (∀ j : S, j ∉ exceptionSet G color cap R L K S n x e →
        f j.val = labelBump (label G color cap R) (originalLabel G color cap x) L K j.val) ∧
      (∀ j : S, j ∉ exceptionSet G color cap R L K S n (G.move x e) (G.reverse e) →
        f j.val = -labelBump (label G color cap R) (originalLabel G color cap (G.move x e)) L K j.val) := by sorry
