-- Prove2me | Theorems.Thm_OAI_DiscreteFree_PortGraph_label_support_le
-- name    : OAI.DiscreteFree.PortGraph.label_support_le
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T09:48:47.810954+00:00
-- url     : https://prove2.me/theorems/0571829f-48da-4adc-b680-6d9567f3390a
-- title:
--   Only boundedly many colors lie within capped walk distance of a vertex in a port graph
-- statement:
--   Let $G$ be a port graph on a vertex set $X$ with a finite port set $D$: an involution $e\mapsto\bar e$ of $D$ and a move map $X\times D\to X$, $(x,e)\mapsto x\cdot e$, such that $(x\cdot e)\cdot\bar e=x$ for all $x\in X$ and $e\in D$. A word $w=e_1e_2\cdots e_k$ of ports (an arbitrary finite list, not necessarily reduced) moves $x$ along a walk to $x\cdot w=(\cdots((x\cdot e_1)\cdot e_2)\cdots)\cdot e_k$, and $|w|=k$ is its length. Let $\chi\colon X\to C$ be a coloring with values in a finite set $C$ and let $\mathrm{cap}\in\mathbb{N}$. The capped label of a vertex $x$ in color $i\in C$ is
--   $$
--   \ell_i(x)=\min\Bigl(\{\mathrm{cap}\}\cup\bigl\{|w|:\ w \text{ a port word with } \chi(x\cdot w)=i\bigr\}\Bigr)\in\{0,1,\dots,\mathrm{cap}\},
--   $$
--   the length of a shortest walk from $x$ to a vertex of color $i$, truncated at $\mathrm{cap}$.
--
--   **Theorem.** For every vertex $x\in X$,
--   $$
--   \#\{\,i\in C:\ \ell_i(x)<\mathrm{cap}\,\}\ \le\ \#\{\,w\in D^{*}:\ |w|\le\mathrm{cap}\,\},
--   $$
--   where $D^{*}$ is the set of all finite words over $D$; the right-hand side equals $\sum_{k=0}^{\mathrm{cap}}|D|^k$.
--
--   So the number of colors that can be reached from one vertex by a walk shorter than the cap is bounded independently of the number of colors and of the graph. In the metric-block construction the label vector $(\ell_i(x))_{i\in C}$ serves as an anchor coordinate, and this bound limits the number of its "support colors", the coordinates that differ from the default value $\mathrm{cap}$.
--
--   **Formalization Note** The left side is `Nat.card` of a subtype of the finite type `C`, hence the genuine number of such colors; the right side is `Fintype.card (BoundedWords D cap)`, the number of lists of ports of length at most `cap` (the geometric-sum formula is a standard identity, not part of the Lean statement). The label is `G.label color cap i x`, defined with `Nat.find`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/LipschitzFree/PortGraphs.lean#L175-L191

import Mathlib
import Definitions.Def_DiscreteLipschitzFree
import Definitions.Def_OAI_Analysis_LipschitzFree_PortGraphs

open OAI OAI.DiscreteFree OAI.DiscreteFree.PortGraph
open scoped BigOperators ENNReal
open scoped BigOperators Classical
variable {X D : Type*} [Fintype D] (G : PortGraph X D)

theorem OAI.DiscreteFree.PortGraph.label_support_le {C : Type*} [Fintype C] (color : X → C) (cap : ℕ)
    (x : X) : Nat.card {i : C // G.label color cap i x < cap} ≤
      Fintype.card (BoundedWords D cap) := by sorry
