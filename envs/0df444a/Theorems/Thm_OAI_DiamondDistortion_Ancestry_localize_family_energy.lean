-- Prove2me | Theorems.Thm_OAI_DiamondDistortion_Ancestry_localize_family_energy
-- name    : OAI.DiamondDistortion.Ancestry.localize_family_energy
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T00:54:58.185741+00:00
-- url     : https://prove2.me/theorems/b7f6c104-49c2-413c-990d-59b2ed4927db
-- title:
--   Segment tests of functions supported in a finite ancestral set are realized by local families
-- statement:
--   Let $V$ be a set carrying an *ancestry*: a partial order $\le$ (read $a\le b$ as "$a$ is an ancestor of $b$") in which the ancestors of every vertex form a chain, i.e. $a\le c$ and $b\le c$ imply $a\le b$ or $b\le a$. A *segment* is a finite set of the form $[a,b]=\{v\in V:\ a\le v\le b\}$ with $a\le b$, and a *segment family* $\mathcal F=(S_1,\dots,S_n)$ is a finite list of pairwise disjoint segments. For a finitely supported $p:V\to\mathbb{R}$ and a finite $S\subseteq V$ write $p(S)=\sum_{v\in S}p(v)$, and let $\|p\|_{\mathrm{seg}}=\sup_{\mathcal F}\big(\sum_{i}p(S_i)^2\big)^{1/2}$ be the *segment norm*, the supremum over all segment families. A set $H\subseteq V$ is *ancestral* if $a\le b$ and $b\in H$ imply $a\in H$. For a finite $K\subseteq V$, a *local family* of $K$ is a set $\mathcal G$ of pairwise disjoint segments each contained in $K$; there are only finitely many local families of $K$, even when $V$ is infinite.
--
--   Let $K\subseteq V$ be finite and ancestral, let $\mathcal F=(S_1,\dots,S_n)$ be a segment family, and let $p$ be finitely supported with $p(v)=0$ for all $v\notin K$. Then there is a local family $\mathcal G$ of $K$ such that
--
--   $$
--   \sum_{i=1}^{n}p(S_i)^2=\sum_{S\in\mathcal G}p(S)^2 .
--   $$
--
--   Consequently, for functions supported in $K$ the supremum defining $\|p\|_{\mathrm{seg}}$ may be taken over the finitely many local families of $K$ alone. This reduces the segment norm on such functions to a maximum of finitely many Euclidean tests, which is the basis of the finite-dimensional duality arguments for the segment-norm space.
--
--   **Formalization Note** The vertex set is a type with an `Ancestry` instance and $K$ is a `Finset`. A local family is an element of `A.segments.LocalFamily K`: a finset of finsets in the power set of the power set of $K$ whose members are segments and pairwise disjoint. Its members, being elements of a set, are distinct, and the sum on the right runs over them (`A.segments.LocalIndex G`).
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/DiamondDistortion/Ancestry.lean#L689-L758

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

theorem OAI.DiamondDistortion.Ancestry.localize_family_energy {K : Finset ι} (hK : A.Ancestral (K : Set ι))
    (F : A.segments.Family) (p : ι →₀ ℝ) (hp : ∀ v, v ∉ K → p v = 0) :
    ∃ G : A.segments.LocalFamily K,
      (∑ i, (∑ v ∈ F.seg i, p v) ^ 2) =
        ∑ S : A.segments.LocalIndex G, (∑ v ∈ S.val, p v) ^ 2 := by sorry
