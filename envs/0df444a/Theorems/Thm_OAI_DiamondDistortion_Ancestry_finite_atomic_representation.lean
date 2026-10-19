-- Prove2me | Theorems.Thm_OAI_DiamondDistortion_Ancestry_finite_atomic_representation
-- name    : OAI.DiamondDistortion.Ancestry.finite_atomic_representation
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T00:55:31.885897+00:00
-- url     : https://prove2.me/theorems/f3705b30-77c0-4ca8-8a19-6f1e0ca67c47
-- title:
--   Finite atomic representation of dual unit-ball functionals on a finite ancestral set
-- statement:
--   Let $V$ be a set carrying an *ancestry*: a partial order $\le$ (read $a\le b$ as "$a$ is an ancestor of $b$") in which the ancestors of every vertex form a chain, i.e. $a\le c$ and $b\le c$ imply $a\le b$ or $b\le a$. A *segment* is a finite set of the form $[a,b]=\{v\in V:\ a\le v\le b\}$ with $a\le b$, and a *segment family* $\mathcal F=(S_1,\dots,S_n)$ is a finite list of pairwise disjoint segments. For a finitely supported $p:V\to\mathbb{R}$ and a finite $S\subseteq V$ write $p(S)=\sum_{v\in S}p(v)$, and let $\|p\|_{\mathrm{seg}}=\sup_{\mathcal F}\big(\sum_{i}p(S_i)^2\big)^{1/2}$ be the *segment norm*, the supremum over all segment families.
--
--   Let $J$ be the completion of the space of finitely supported functions $V\to\mathbb{R}$ under $\|\cdot\|_{\mathrm{seg}}$; write $\hat p\in J$ for the image of $p$ and $e_v\in J$ for the image of the indicator of $\{v\}$. Let $J^*$ be the space of all continuous linear functionals on $J$, with the operator norm $\|x\|=\sup_{\|u\|\le1}|x(u)|$, and let $e_v^*\in J^*$ be the coordinate functional, i.e. the continuous extension of $p\mapsto p(v)$. For a finite $H\subseteq V$ the head and tail projections on $J^*$ are $P_Hx=\sum_{v\in H}x(e_v)\,e_v^*$ and $Q_Hx=x-P_Hx$. A set $H\subseteq V$ is *ancestral* if $a\le b$ and $b\in H$ imply $a\in H$. For a finite $K\subseteq V$, a *local family* of $K$ is a set $\mathcal G$ of pairwise disjoint segments each contained in $K$; there are finitely many of them. For a local family $\mathcal G$ let $\mathbb{R}^{\mathcal G}$ be the Euclidean space of vectors $a=(a_S)_{S\in\mathcal G}$ with norm $\|a\|_2$.
--
--   Let $K\subseteq V$ be finite and ancestral, and let $x\in J^*$ with $\|x\|\le1$. Then there are vectors $c_{\mathcal G}\in\mathbb{R}^{\mathcal G}$, one for each local family $\mathcal G$ of $K$, such that
--
--   $$
--   \sum_{\mathcal G}\|c_{\mathcal G}\|_2\le1\qquad\text{and}\qquad x(e_v)=\sum_{\mathcal G}\ \sum_{S\in\mathcal G,\ v\in S}c_{\mathcal G}(S)\quad\text{for every }v\in K .
--   $$
--
--   Equivalently, with $\sigma_S=\sum_{v\in S}e_v^*$, the finite combination $\sum_{\mathcal G}\sum_{S\in\mathcal G}c_{\mathcal G}(S)\,\sigma_S$ agrees with $x$ on every unit vector $e_v$ with $v\in K$. Each block $\sum_{S\in\mathcal G}a_S\sigma_S$ with $\|a\|_2\le1$ is an "atom" made of disjoint segments. The theorem says that, seen through the coordinates in $K$, every functional of the dual unit ball is a combination of such atoms with total mass at most one. It turns an arbitrary norm-one functional into a finite probability law of explicit atoms, without assuming any representation theorem for the dual.
--
--   **Formalization Note** The vertex set is a type with an `Ancestry` instance and $K$ is a `Finset`. The family $(c_{\mathcal G})$ is an element of `A.segments.coefficientBall K 1`, the set of $c$ with $\sum_{\mathcal G}\|c_{\mathcal G}\|_2\le1$. The coordinate condition is `A.segments.totalMap K c = fun v : K => x (A.segments.unitVector v.val)`, where `totalMap` sends $c$ to $\big(\sum_{\mathcal G}\sum_{S\in\mathcal G,\,v\in S}c_{\mathcal G}(S)\big)_{v\in K}$. $J^*$ is the full continuous dual of the completion.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/DiamondDistortion/Ancestry.lean#L777-L823

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

theorem OAI.DiamondDistortion.Ancestry.finite_atomic_representation {K : Finset ι} (hK : A.Ancestral (K : Set ι))
    (x : A.segments.Dual) (hx : ‖x‖ ≤ 1) :
    ∃ c ∈ A.segments.coefficientBall K 1,
      A.segments.totalMap K c = fun v : K => x (A.segments.unitVector v.val) := by sorry
