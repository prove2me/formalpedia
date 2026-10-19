-- Prove2me | Theorems.Thm_OAI_DiamondDistortion_Ancestry_opposite_matching_le
-- name    : OAI.DiamondDistortion.Ancestry.opposite_matching_le
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T00:51:24.948999+00:00
-- url     : https://prove2.me/theorems/1b60921e-7e90-46e6-8904-fb3300a4f2a2
-- title:
--   Opposite-sign segment sums matched across two families are paid for by the two slacks
-- statement:
--   Let $V$ be a set carrying an *ancestry*: a partial order $\le$ (read $a\le b$ as "$a$ is an ancestor of $b$") in which the ancestors of every vertex form a chain, i.e. $a\le c$ and $b\le c$ imply $a\le b$ or $b\le a$. A *segment* is a finite set of the form $[a,b]=\{v\in V:\ a\le v\le b\}$ with $a\le b$, and a *segment family* $\mathcal F=(S_1,\dots,S_n)$ is a finite list of pairwise disjoint segments. For a finitely supported $p:V\to\mathbb{R}$ and a finite $S\subseteq V$ write $p(S)=\sum_{v\in S}p(v)$, and let $\|p\|_{\mathrm{seg}}=\sup_{\mathcal F}\big(\sum_{i}p(S_i)^2\big)^{1/2}$ be the *segment norm*, the supremum over all segment families. A set $H\subseteq V$ is *ancestral* if $a\le b$ and $b\in H$ imply $a\in H$.
--
--   Let $\kappa$ be a finite set and $H\subseteq V$ an ancestral set, and let $p:V\to\mathbb{R}$ be finitely supported with $p(v)=0$ for all $v\notin H$. Let $\mathcal F=(S_1,\dots,S_n)$ and $\mathcal G=(T_1,\dots,T_m)$ be segment families, let $e_F:\kappa\to\{1,\dots,n\}$ and $e_G:\kappa\to\{1,\dots,m\}$ be injective, and let $g:\kappa\to V$. Assume that for every $a\in\kappa$:
--
--   - $g_a\notin H$, $g_a\in S_{e_F(a)}$ and $g_a\in T_{e_G(a)}$;
--   - $p(S_{e_F(a)})\,p(T_{e_G(a)})<0$.
--
--   Then
--
--   $$
--   2\sum_{a\in\kappa}\big|p(S_{e_F(a)})\,p(T_{e_G(a)})\big|\le\Big(\|p\|_{\mathrm{seg}}^2-\sum_{i=1}^{n}p(S_i)^2\Big)+\Big(\|p\|_{\mathrm{seg}}^2-\sum_{j=1}^{m}p(T_j)^2\Big).
--   $$
--
--   Here $H$ is a head carrying all the mass of $p$, and each $g_a$ is a vertex outside the head through which a segment of $\mathcal F$ and a segment of $\mathcal G$ both pass, distinct crossings using distinct segments in each family. Whenever the two segment sums at such a crossing have opposite signs, their product is charged to the combined slacks of the two families. This is the simultaneous boundary-cancellation estimate behind the opposite-crossing bounds at the gates of a head.
--
--   **Formalization Note** The vertex set is a type with an `Ancestry` instance, $H$ is a `Set`, $p$ is a `ι →₀ ℝ`, and $\|p\|_{\mathrm{seg}}$ is `A.segments.primalSeminorm p`. The injections are embeddings `κ ↪ Fin F.n` and `κ ↪ Fin G.n`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/DiamondDistortion/Ancestry.lean#L310-L374

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

theorem OAI.DiamondDistortion.Ancestry.opposite_matching_le {κ : Type*} [Fintype κ]
    {H : Set ι} (hH : A.Ancestral H) (p : ι →₀ ℝ)
    (hp : ∀ v, v ∉ H → p v = 0) (F G : A.segments.Family)
    (eF : κ ↪ Fin F.n) (eG : κ ↪ Fin G.n) (g : κ → ι)
    (hgH : ∀ a, g a ∉ H) (hgF : ∀ a, g a ∈ F.seg (eF a))
    (hgG : ∀ a, g a ∈ G.seg (eG a))
    (hopp : ∀ a, (∑ v ∈ F.seg (eF a), p v) * (∑ v ∈ G.seg (eG a), p v) < 0) :
    2 * (∑ a, |(∑ v ∈ F.seg (eF a), p v) * (∑ v ∈ G.seg (eG a), p v)|) ≤
      ((A.segments.primalSeminorm p) ^ 2 - ∑ i, (∑ v ∈ F.seg i, p v) ^ 2) +
      ((A.segments.primalSeminorm p) ^ 2 - ∑ j, (∑ v ∈ G.seg j, p v) ^ 2) := by sorry
