-- Prove2me | Theorems.Thm_OAI_DiamondDistortion_Ancestry_replaced_tail_eq
-- name    : OAI.DiamondDistortion.Ancestry.replaced_tail_eq
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T00:53:13.054902+00:00
-- url     : https://prove2.me/theorems/2aba90a2-8b75-4081-b0db-b85ce6ccdc89
-- title:
--   The tail of a segment-mass functional decomposes into crossing tails at the gates of the head
-- statement:
--   Let $V$ be a set carrying an *ancestry*: a partial order $\le$ (read $a\le b$ as "$a$ is an ancestor of $b$") in which the ancestors of every vertex form a chain, i.e. $a\le c$ and $b\le c$ imply $a\le b$ or $b\le a$. A *segment* is a finite set of the form $[a,b]=\{v\in V:\ a\le v\le b\}$ with $a\le b$, and a *segment family* $\mathcal F=(S_1,\dots,S_n)$ is a finite list of pairwise disjoint segments. For a finitely supported $p:V\to\mathbb{R}$ and a finite $S\subseteq V$ write $p(S)=\sum_{v\in S}p(v)$, and let $\|p\|_{\mathrm{seg}}=\sup_{\mathcal F}\big(\sum_{i}p(S_i)^2\big)^{1/2}$ be the *segment norm*, the supremum over all segment families.
--
--   Let $J$ be the completion of the space of finitely supported functions $V\to\mathbb{R}$ under $\|\cdot\|_{\mathrm{seg}}$; write $\hat p\in J$ for the image of $p$ and $e_v\in J$ for the image of the indicator of $\{v\}$. Let $J^*$ be the space of all continuous linear functionals on $J$, with the operator norm $\|x\|=\sup_{\|u\|\le1}|x(u)|$, and let $e_v^*\in J^*$ be the coordinate functional, i.e. the continuous extension of $p\mapsto p(v)$. For a finite $H\subseteq V$ the head and tail projections on $J^*$ are $P_Hx=\sum_{v\in H}x(e_v)\,e_v^*$ and $Q_Hx=x-P_Hx$. For a finite $S\subseteq V$ let $\sigma_S=\sum_{v\in S}e_v^*\in J^*$, so that $\sigma_S(\hat p)=p(S)$. A set $H\subseteq V$ is *ancestral* if $a\le b$ and $b\in H$ imply $a\in H$. A *gate* of $H$ is a vertex $g\notin H$ all of whose strict ancestors lie in $H$.
--
--   Let $H$ and $K$ be finite ancestral subsets of $V$, and let $\Gamma$ be the finite set of gates of $H$ that lie in $K$. Let $\mathcal F=(S_1,\dots,S_n)$ be a segment family with $S_i\subseteq K$ for all $i$, and let $p$ be finitely supported with $p(v)=0$ for all $v\notin H$. For $g\in V$ put $\beta_{\mathcal F}(g)=p(S_i)$ and $\tau_{\mathcal F}(g)=S_i\setminus H$ if $g$ lies in the member $S_i$ (which is unique by disjointness), and $\beta_{\mathcal F}(g)=0$, $\tau_{\mathcal F}(g)=\emptyset$ if $g$ lies in no member. Then
--
--   $$
--   Q_H\Big(\sum_{i=1}^{n}p(S_i)\,\sigma_{S_i}\Big)=\sum_{g\in\Gamma}\beta_{\mathcal F}(g)\,\sigma_{\tau_{\mathcal F}(g)} .
--   $$
--
--   The functional $\sum_ip(S_i)\sigma_{S_i}$ replaces each segment by its total $p$-mass. The identity says that its part outside the head $H$ has no contribution from segments lying wholly outside $H$; all of it is carried by the tails $S_i\setminus H$ of the segments that cross a gate of $H$, each weighted by the mass of the segment it continues. Since tails through distinct gates lie above distinct gates and are therefore disjoint, this makes the tails of such replacement functionals estimable gate by gate.
--
--   **Formalization Note** The vertex set is a type with an `Ancestry` instance and $H,K$ are `Finset`s. $\sigma_S$ is `A.segments.segmentFunctional S`, combinations $\sum_ia_i\sigma_{S_i}$ are `A.segments.combine`, $Q_H$ is `A.segments.tailDual H`, $\Gamma$ is the subtype of `A.gateSet H K`, $\beta_{\mathcal F}$ is `A.boundaryCoeff F p` and $\tau_{\mathcal F}$ is `A.tailAt F H`. The space $J^*$ is the full continuous dual of the completion.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/DiamondDistortion/Ancestry.lean#L581-L641

import Mathlib
import Definitions.Def_DiamondDistortion
import Definitions.Def_OAI_Analysis_DiamondDistortion_SegmentNorm
import Definitions.Def_OAI_Analysis_DiamondDistortion_Ancestry

open OAI OAI.DiamondDistortion OAI.DiamondDistortion.Ancestry
universe u v
open scoped BigOperators Classical Topology
open Set
open scoped Classical
attribute [local instance] OAI.DiamondDistortion.Ancestry.instPartialOrder
variable {ι : Type*} [A : Ancestry ι]

theorem OAI.DiamondDistortion.Ancestry.replaced_tail_eq {H K : Finset ι} (hH : A.Ancestral (H : Set ι))
    (hK : A.Ancestral (K : Set ι)) (F : A.segments.Family)
    (hFK : ∀ i, F.seg i ⊆ K) (p : ι →₀ ℝ) (hp : ∀ v, v ∉ H → p v = 0) :
    A.segments.tailDual H (A.segments.combine F.seg (fun i => ∑ v ∈ F.seg i, p v)) =
      A.segments.combine (fun g : A.gateSet H K => A.tailAt F H g.val)
        (fun g : A.gateSet H K => A.boundaryCoeff F p g.val) := by sorry
