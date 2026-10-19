-- Prove2me | Theorems.Thm_OAI_DiamondDistortion_Forest_full_dual_approximation
-- name    : OAI.DiamondDistortion.Forest.full_dual_approximation
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T01:05:17.993944+00:00
-- url     : https://prove2.me/theorems/785e0a0c-8ca4-4bfb-b6a9-cbb09e5f1206
-- title:
--   Every functional on the James space of the finite-height forest is approximated by finite ancestral heads
-- statement:
--   The *forest* $\mathcal F$ consists of the pairs $(h,w)$ where $h\ge1$ is an integer and $w$ is a finite word over the alphabet $\mathbb{N}$ of length $|w|\le h$. It is partially ordered by $(h,w)\le(h',w')$ if and only if $h=h'$ and $w$ is a prefix of $w'$. Thus $\mathcal F$ is the disjoint union over $h\ge1$ of the countably branching trees of height $h$, and the predecessors of every node form a chain. A *segment* is an order interval $[a,b]=\{v:a\le v\le b\}$ with $a\le b$ that is a finite set. For a finitely supported $p\colon\mathcal F\to\mathbb{R}$ let
--   $$\|p\|=\sup_{S_1,\dots,S_n}\Bigl(\sum_{i=1}^{n}\Bigl(\sum_{v\in S_i}p(v)\Bigr)^2\Bigr)^{1/2},$$
--   the supremum over all finite families ($n\ge0$) of pairwise disjoint segments. Let $J_{\mathcal F}$ be the completion of the finitely supported functions under this norm and $J_{\mathcal F}^*$ its full dual (all continuous linear functionals, with the operator norm). Write $e_v$ for the indicator of the node $v$, $e_v^*$ for the coordinate functional (the continuous extension of $p\mapsto p(v)$), and for a finite set $H\subseteq\mathcal F$ put $Q_Hx=x-\sum_{v\in H}x(e_v)\,e_v^*$. A set $H$ is *ancestral* if it is downward closed: $a\le b$ and $b\in H$ imply $a\in H$.
--
--   **Theorem.** For every $x\in J_{\mathcal F}^*$ and every $\varepsilon>0$ there is a finite ancestral set $H\subseteq\mathcal F$ with
--   $$\|Q_Hx\|_{J_{\mathcal F}^*}<\varepsilon .$$
--
--   So the whole dual of the forest space, not only the closed span of the coordinate functionals, has the finite-head approximation property; no extra hypothesis on $x$ is imposed. This is the approximation input that makes the quadratic separated-lens inequality available for $J_{\mathcal F}^*$.
--
--   **Formalization Note** Nodes are `ForestNode`, a subtype of `ℕ × List ℕ`, with the order `forestAncestry` given by `ForestAncestor`; the segment system is `forestSegments`, $J_{\mathcal F}^*$ is `forestSegments.Dual` (the type abbreviated `ForestDual`), $Q_H$ is `forestSegments.tailDual H` for `H : Finset ForestNode`, and ancestral sets are `Ancestry.Ancestral (A := forestAncestry)`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/DiamondDistortion/ForestModels.lean#L192-L267

import Mathlib
import Definitions.Def_DiamondDistortion
import Definitions.Def_OAI_Analysis_DiamondDistortion_SegmentNorm
import Definitions.Def_OAI_Analysis_DiamondDistortion_Ancestry
import Definitions.Def_OAI_Analysis_DiamondDistortion_Orthogonality
import Definitions.Def_OAI_Analysis_DiamondDistortion_ForestModels

open OAI OAI.DiamondDistortion OAI.DiamondDistortion.Forest
universe u v
open scoped BigOperators Classical Topology
open Set

theorem OAI.DiamondDistortion.Forest.full_dual_approximation (x : forestSegments.Dual) {ε : ℝ} (hε : 0 < ε) :
    ∃ H : Finset ForestNode, Ancestry.Ancestral (A := forestAncestry) (H : Set ForestNode) ∧
      ‖forestSegments.tailDual H x‖ < ε := by sorry
