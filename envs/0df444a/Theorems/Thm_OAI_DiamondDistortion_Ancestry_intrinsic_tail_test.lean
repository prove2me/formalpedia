-- Prove2me | Theorems.Thm_OAI_DiamondDistortion_Ancestry_intrinsic_tail_test
-- name    : OAI.DiamondDistortion.Ancestry.intrinsic_tail_test
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T00:57:30.451986+00:00
-- url     : https://prove2.me/theorems/c2b0be95-a5e2-4e3c-a159-404167dab33d
-- title:
--   Intrinsic tail bound in the dual of the segment-norm space
-- statement:
--   Let $V$ be a set carrying an *ancestry*: a partial order $\le$ (read $a\le b$ as "$a$ is an ancestor of $b$") in which the ancestors of every vertex form a chain, i.e. $a\le c$ and $b\le c$ imply $a\le b$ or $b\le a$. A *segment* is a finite set of the form $[a,b]=\{v\in V:\ a\le v\le b\}$ with $a\le b$, and a *segment family* $\mathcal F=(S_1,\dots,S_n)$ is a finite list of pairwise disjoint segments. For a finitely supported $p:V\to\mathbb{R}$ and a finite $S\subseteq V$ write $p(S)=\sum_{v\in S}p(v)$, and let $\|p\|_{\mathrm{seg}}=\sup_{\mathcal F}\big(\sum_{i}p(S_i)^2\big)^{1/2}$ be the *segment norm*, the supremum over all segment families.
--
--   Let $J$ be the completion of the space of finitely supported functions $V\to\mathbb{R}$ under $\|\cdot\|_{\mathrm{seg}}$; write $\hat p\in J$ for the image of $p$ and $e_v\in J$ for the image of the indicator of $\{v\}$. Let $J^*$ be the space of all continuous linear functionals on $J$, with the operator norm $\|x\|=\sup_{\|u\|\le1}|x(u)|$, and let $e_v^*\in J^*$ be the coordinate functional, i.e. the continuous extension of $p\mapsto p(v)$. For a finite $H\subseteq V$ the head and tail projections on $J^*$ are $P_Hx=\sum_{v\in H}x(e_v)\,e_v^*$ and $Q_Hx=x-P_Hx$. A set $H\subseteq V$ is *ancestral* if $a\le b$ and $b\in H$ imply $a\in H$.
--
--   Assume that every finite subset of $V$ is contained in some finite ancestral subset of $V$. Let $H\subseteq V$ be finite and ancestral, let $R>0$, and let $x,y\in J^*$ satisfy $x(e_v)=0$ for all $v\notin H$, $\|x+y\|\le R$ and $\|x-y\|\le R$. Let $p$ be finitely supported with $p(v)=0$ for all $v\notin H$ and $\|p\|_{\mathrm{seg}}\le1$. Then
--
--   $$
--   \|Q_Hy\|\le2\sqrt{R^2-x(\hat p)^2} .
--   $$
--
--   This is the finite-head lens estimate with the auxiliary head projection removed, valid for arbitrary functionals of the full dual. No reflexivity, shrinking or other approximation property of the space is assumed. The only structural hypothesis is the exhaustion of finite sets by finite ancestral sets, which holds for instance when every vertex has only finitely many ancestors.
--
--   **Formalization Note** The vertex set is a type with an `Ancestry` instance, $H$ is a `Finset`, $Q_H$ is `A.segments.tailDual H`, $\hat p$ is `A.segments.finiteEmbedding p`, and the square root is the real square root (which is $0$ on negative numbers). The exhaustion hypothesis is `∀ S : Finset ι, ∃ K : Finset ι, S ⊆ K ∧ A.Ancestral (K : Set ι)`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/DiamondDistortion/Ancestry.lean#L1099-L1124

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

theorem OAI.DiamondDistortion.Ancestry.intrinsic_tail_test
    (hfin : ∀ S : Finset ι, ∃ K : Finset ι, S ⊆ K ∧ A.Ancestral (K : Set ι))
    {H : Finset ι} (hH : A.Ancestral (H : Set ι)) {R : ℝ} (hR : 0 < R)
    {x y : A.segments.Dual} (hx : ∀ v, v ∉ H → x (A.segments.unitVector v) = 0)
    (hplus : ‖x+y‖ ≤ R) (hminus : ‖x-y‖ ≤ R)
    (p : ι →₀ ℝ) (hp : ∀ v, v ∉ H → p v = 0) (hpn : A.segments.primalSeminorm p ≤ 1) :
    ‖A.segments.tailDual H y‖ ≤
      2*Real.sqrt (R^2 - (x (A.segments.finiteEmbedding p))^2) := by sorry
