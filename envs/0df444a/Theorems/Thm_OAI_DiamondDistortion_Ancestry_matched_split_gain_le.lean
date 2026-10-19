-- Prove2me | Theorems.Thm_OAI_DiamondDistortion_Ancestry_matched_split_gain_le
-- name    : OAI.DiamondDistortion.Ancestry.matched_split_gain_le
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T00:50:57.109356+00:00
-- url     : https://prove2.me/theorems/1413ddbb-d77e-41a2-891a-37d684429176
-- title:
--   Simultaneous split gain for injectively selected segments of a segment family in a tree order
-- statement:
--   Let $V$ be a set carrying an *ancestry*: a partial order $\le$ (read $a\le b$ as "$a$ is an ancestor of $b$") in which the ancestors of every vertex form a chain, i.e. $a\le c$ and $b\le c$ imply $a\le b$ or $b\le a$. A *segment* is a finite set of the form $[a,b]=\{v\in V:\ a\le v\le b\}$ with $a\le b$, and a *segment family* $\mathcal F=(S_1,\dots,S_n)$ is a finite list of pairwise disjoint segments. For a finitely supported $p:V\to\mathbb{R}$ and a finite $S\subseteq V$ write $p(S)=\sum_{v\in S}p(v)$, and let $\|p\|_{\mathrm{seg}}=\sup_{\mathcal F}\big(\sum_{i}p(S_i)^2\big)^{1/2}$ be the *segment norm*, the supremum over all segment families. For $c\in V$ and a finite $S\subseteq V$ write $S^{\ge c}=\{v\in S:\ c\le v\}$.
--
--   Let $\kappa$ be a finite set, let $\mathcal F=(S_1,\dots,S_n)$ be a segment family, let $e:\kappa\to\{1,\dots,n\}$ be injective, let $c:\kappa\to V$ be arbitrary, and let $p:V\to\mathbb{R}$ be finitely supported. Then
--
--   $$
--   \sum_{i=1}^{n}p(S_i)^2+2\sum_{a\in\kappa}\Big(p\big(S_{e(a)}^{\ge c_a}\big)^2-p\big(S_{e(a)}\big)\,p\big(S_{e(a)}^{\ge c_a}\big)\Big)\le\|p\|_{\mathrm{seg}}^2 .
--   $$
--
--   Here $e$ selects some members of the family, each at most once, and $c_a$ is a cut point for the selected segment $S_{e(a)}$ (it need not lie in that segment). With $s_a=p(S_{e(a)})$, $t_a=p(S_{e(a)}^{\ge c_a})$ and $h_a=s_a-t_a$, the quantity $2(t_a^2-s_at_a)=-2h_at_a$ equals $h_a^2+t_a^2-s_a^2$, the increase of the sum of squares when $S_{e(a)}$ is split into the part not above $c_a$ and the part above $c_a$. The inequality says that these gains, taken over all selected segments simultaneously, are paid for by the slack $\|p\|_{\mathrm{seg}}^2-\sum_ip(S_i)^2$ of the family. It is the device used to charge opposite-sign crossings of two segment families to their slacks.
--
--   **Formalization Note** The vertex set is a type with an `Ancestry` instance, segments are those of `Ancestry.segments` (nonempty finite order intervals), $p$ is a `ι →₀ ℝ`, and $\|p\|_{\mathrm{seg}}$ is `A.segments.primalSeminorm p`. Members of the family are indexed by `Fin F.n`, the selection is an embedding `κ ↪ Fin F.n`, and $S^{\ge c}$ is `(F.seg (e a)).filter (fun v => c a ≤ v)`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/DiamondDistortion/Ancestry.lean#L270-L308

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

theorem OAI.DiamondDistortion.Ancestry.matched_split_gain_le {κ : Type*} [Fintype κ]
    (F : A.segments.Family) (e : κ ↪ Fin F.n) (c : κ → ι) (p : ι →₀ ℝ) :
    (∑ i, (∑ v ∈ F.seg i, p v) ^ 2) +
      2 * (∑ a, ((∑ v ∈ (F.seg (e a)).filter (fun v => c a ≤ v), p v) ^ 2 -
        (∑ v ∈ F.seg (e a), p v) *
          (∑ v ∈ (F.seg (e a)).filter (fun v => c a ≤ v), p v))) ≤
      (A.segments.primalSeminorm p) ^ 2 := by sorry
