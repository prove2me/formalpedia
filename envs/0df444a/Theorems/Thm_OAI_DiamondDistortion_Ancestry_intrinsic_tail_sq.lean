-- Prove2me | Theorems.Thm_OAI_DiamondDistortion_Ancestry_intrinsic_tail_sq
-- name    : OAI.DiamondDistortion.Ancestry.intrinsic_tail_sq
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T00:58:02.379509+00:00
-- url     : https://prove2.me/theorems/afb7975b-f462-4655-a9e7-f96bd2f1b97e
-- title:
--   Quadratic lens inequality $\|Q_Hy\|^2+4\|x\|^2\le4R^2$ in the dual of the segment-norm space
-- statement:
--   Let $V$ be a set carrying an *ancestry*: a partial order $\le$ (read $a\le b$ as "$a$ is an ancestor of $b$") in which the ancestors of every vertex form a chain, i.e. $a\le c$ and $b\le c$ imply $a\le b$ or $b\le a$. A *segment* is a finite set of the form $[a,b]=\{v\in V:\ a\le v\le b\}$ with $a\le b$, and a *segment family* $\mathcal F=(S_1,\dots,S_n)$ is a finite list of pairwise disjoint segments. For a finitely supported $p:V\to\mathbb{R}$ and a finite $S\subseteq V$ write $p(S)=\sum_{v\in S}p(v)$, and let $\|p\|_{\mathrm{seg}}=\sup_{\mathcal F}\big(\sum_{i}p(S_i)^2\big)^{1/2}$ be the *segment norm*, the supremum over all segment families.
--
--   Let $J$ be the completion of the space of finitely supported functions $V\to\mathbb{R}$ under $\|\cdot\|_{\mathrm{seg}}$; write $\hat p\in J$ for the image of $p$ and $e_v\in J$ for the image of the indicator of $\{v\}$. Let $J^*$ be the space of all continuous linear functionals on $J$, with the operator norm $\|x\|=\sup_{\|u\|\le1}|x(u)|$, and let $e_v^*\in J^*$ be the coordinate functional, i.e. the continuous extension of $p\mapsto p(v)$. For a finite $H\subseteq V$ the head and tail projections on $J^*$ are $P_Hx=\sum_{v\in H}x(e_v)\,e_v^*$ and $Q_Hx=x-P_Hx$. A set $H\subseteq V$ is *ancestral* if $a\le b$ and $b\in H$ imply $a\in H$.
--
--   Assume that every finite subset of $V$ is contained in some finite ancestral subset of $V$. Let $H\subseteq V$ be finite and ancestral, let $R\ge0$, and let $x,y\in J^*$ satisfy $x(e_v)=0$ for all $v\notin H$, $\|x+y\|\le R$ and $\|x-y\|\le R$. Then
--
--   $$
--   \|Q_Hy\|^2+4\|x\|^2\le4R^2 .
--   $$
--
--   In words: if both $x+y$ and $x-y$ lie in the ball of radius $R$ and $x$ only sees the coordinates of the finite head $H$, then $y$ can have a large part beyond $H$ only if $x$ is correspondingly small. This dimension-free lens inequality is the input for a separated-lens estimate, which in turn serves the lower bounds for the distortion of diamond graphs into duals of segment-norm spaces on trees.
--
--   **Formalization Note** The vertex set is a type with an `Ancestry` instance, $H$ is a `Finset`, $Q_H$ is `A.segments.tailDual H`, and $J^*$ is the full continuous dual of the completion. The exhaustion hypothesis is `∀ S : Finset ι, ∃ K : Finset ι, S ⊆ K ∧ A.Ancestral (K : Set ι)`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/DiamondDistortion/Ancestry.lean#L1134-L1183

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

theorem OAI.DiamondDistortion.Ancestry.intrinsic_tail_sq
    (hfin : ∀ S : Finset ι, ∃ K : Finset ι, S ⊆ K ∧ A.Ancestral (K : Set ι))
    {H : Finset ι} (hH : A.Ancestral (H : Set ι)) {R : ℝ} (hR : 0 ≤ R)
    {x y : A.segments.Dual} (hx : ∀ v, v ∉ H → x (A.segments.unitVector v) = 0)
    (hplus : ‖x+y‖ ≤ R) (hminus : ‖x-y‖ ≤ R) :
    ‖A.segments.tailDual H y‖^2 + 4*‖x‖^2 ≤ 4*R^2 := by sorry
