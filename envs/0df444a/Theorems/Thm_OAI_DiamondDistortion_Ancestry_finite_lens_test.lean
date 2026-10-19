-- Prove2me | Theorems.Thm_OAI_DiamondDistortion_Ancestry_finite_lens_test
-- name    : OAI.DiamondDistortion.Ancestry.finite_lens_test
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T00:56:55.306223+00:00
-- url     : https://prove2.me/theorems/dad2ba7d-044e-4eb0-9e87-35bdab03b2f9
-- title:
--   Finite-head lens bound: the tail of $P_Ky$ when $x+y$ and $x-y$ have norm at most $R$
-- statement:
--   Let $V$ be a set carrying an *ancestry*: a partial order $\le$ (read $a\le b$ as "$a$ is an ancestor of $b$") in which the ancestors of every vertex form a chain, i.e. $a\le c$ and $b\le c$ imply $a\le b$ or $b\le a$. A *segment* is a finite set of the form $[a,b]=\{v\in V:\ a\le v\le b\}$ with $a\le b$, and a *segment family* $\mathcal F=(S_1,\dots,S_n)$ is a finite list of pairwise disjoint segments. For a finitely supported $p:V\to\mathbb{R}$ and a finite $S\subseteq V$ write $p(S)=\sum_{v\in S}p(v)$, and let $\|p\|_{\mathrm{seg}}=\sup_{\mathcal F}\big(\sum_{i}p(S_i)^2\big)^{1/2}$ be the *segment norm*, the supremum over all segment families.
--
--   Let $J$ be the completion of the space of finitely supported functions $V\to\mathbb{R}$ under $\|\cdot\|_{\mathrm{seg}}$; write $\hat p\in J$ for the image of $p$ and $e_v\in J$ for the image of the indicator of $\{v\}$. Let $J^*$ be the space of all continuous linear functionals on $J$, with the operator norm $\|x\|=\sup_{\|u\|\le1}|x(u)|$, and let $e_v^*\in J^*$ be the coordinate functional, i.e. the continuous extension of $p\mapsto p(v)$. For a finite $H\subseteq V$ the head and tail projections on $J^*$ are $P_Hx=\sum_{v\in H}x(e_v)\,e_v^*$ and $Q_Hx=x-P_Hx$. A set $H\subseteq V$ is *ancestral* if $a\le b$ and $b\in H$ imply $a\in H$.
--
--   Let $H\subseteq K$ be finite ancestral subsets of $V$, let $R>0$, and let $x,y\in J^*$ satisfy $x(e_v)=0$ for all $v\notin H$, $\|x+y\|\le R$ and $\|x-y\|\le R$. Let $p$ be finitely supported with $p(v)=0$ for all $v\notin H$ and $\|p\|_{\mathrm{seg}}\le1$. Then
--
--   $$
--   \|Q_H(P_Ky)\|\le2\sqrt{R^2-x(\hat p)^2} .
--   $$
--
--   The functionals $x\pm y$ form a "lens" around $x$, and the estimate bounds the part of $y$ that is visible in the coordinates of $K$ but lies beyond the head $H$. It is the finite-head version of the intrinsic tail estimate for the dual of the segment-norm space; letting $K$ grow removes the head projection $P_K$.
--
--   **Formalization Note** The vertex set is a type with an `Ancestry` instance, $H,K$ are `Finset`s, $P_K$ is `A.segments.headDual K`, $Q_H$ is `A.segments.tailDual H`, $\hat p$ is `A.segments.finiteEmbedding p`, and the square root is the real square root (which is $0$ on negative numbers).
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/DiamondDistortion/Ancestry.lean#L1071-L1097

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

theorem OAI.DiamondDistortion.Ancestry.finite_lens_test {H K : Finset ι}
    (hH : A.Ancestral (H : Set ι)) (hK : A.Ancestral (K : Set ι)) (hHK : H ⊆ K)
    {R : ℝ} (hR : 0 < R) {x y : A.segments.Dual}
    (hx : ∀ v, v ∉ H → x (A.segments.unitVector v) = 0)
    (hplus : ‖x+y‖ ≤ R) (hminus : ‖x-y‖ ≤ R)
    (p : ι →₀ ℝ) (hp : ∀ v, v ∉ H → p v = 0) (hpn : A.segments.primalSeminorm p ≤ 1) :
    ‖A.segments.tailDual H (A.segments.headDual K y)‖ ≤
      2*Real.sqrt (R^2 - (x (A.segments.finiteEmbedding p))^2) := by sorry
