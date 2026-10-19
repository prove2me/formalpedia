-- Prove2me | Theorems.Thm_OAI_DiamondDistortion_Ancestry_primal_filter_tail_le
-- name    : OAI.DiamondDistortion.Ancestry.primal_filter_tail_le
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T00:54:22.411276+00:00
-- url     : https://prove2.me/theorems/b70d7a3a-a8d7-42f5-8221-0c6c6855f4f1
-- title:
--   Restriction to the complement of an ancestral head does not increase the segment norm
-- statement:
--   Let $V$ be a set carrying an *ancestry*: a partial order $\le$ (read $a\le b$ as "$a$ is an ancestor of $b$") in which the ancestors of every vertex form a chain, i.e. $a\le c$ and $b\le c$ imply $a\le b$ or $b\le a$. A *segment* is a finite set of the form $[a,b]=\{v\in V:\ a\le v\le b\}$ with $a\le b$, and a *segment family* $\mathcal F=(S_1,\dots,S_n)$ is a finite list of pairwise disjoint segments. For a finitely supported $p:V\to\mathbb{R}$ and a finite $S\subseteq V$ write $p(S)=\sum_{v\in S}p(v)$, and let $\|p\|_{\mathrm{seg}}=\sup_{\mathcal F}\big(\sum_{i}p(S_i)^2\big)^{1/2}$ be the *segment norm*, the supremum over all segment families. A set $H\subseteq V$ is *ancestral* if $a\le b$ and $b\in H$ imply $a\in H$. For a finitely supported $u$ let $u\mathbf 1_{V\setminus H}$ denote its restriction to the complement of $H$, equal to $u$ off $H$ and to $0$ on $H$.
--
--   If $H\subseteq V$ is ancestral (not necessarily finite) and $u:V\to\mathbb{R}$ is finitely supported, then
--
--   $$
--   \|u\mathbf 1_{V\setminus H}\|_{\mathrm{seg}}\le\|u\|_{\mathrm{seg}} .
--   $$
--
--   Together with the analogous statement for the restriction to $H$, this shows that both complementary coordinate projections determined by an ancestral set are contractions for the segment norm. For finite $H$ it extends to the completion, and dually it shows that the tail projections $x\mapsto x-\sum_{v\in H}x(e_v)\,e_v^*$ on the dual space are contractions.
--
--   **Formalization Note** The vertex set is a type with an `Ancestry` instance, $u$ is a `ι →₀ ℝ`, $u\mathbf 1_{V\setminus H}$ is `u.filter (· ∉ H)`, and $\|\cdot\|_{\mathrm{seg}}$ is `A.segments.primalSeminorm`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/DiamondDistortion/Ancestry.lean#L666-L687

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

theorem OAI.DiamondDistortion.Ancestry.primal_filter_tail_le {H : Set ι} (hH : A.Ancestral H) (u : ι →₀ ℝ) :
    A.segments.primalSeminorm (u.filter (· ∉ H)) ≤ A.segments.primalSeminorm u := by sorry
