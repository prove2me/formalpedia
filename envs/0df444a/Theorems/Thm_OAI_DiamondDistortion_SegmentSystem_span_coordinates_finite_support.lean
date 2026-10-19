-- Prove2me | Theorems.Thm_OAI_DiamondDistortion_SegmentSystem_span_coordinates_finite_support
-- name    : OAI.DiamondDistortion.SegmentSystem.span_coordinates_finite_support
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T00:43:20.778813+00:00
-- url     : https://prove2.me/theorems/26139962-0fe8-4c16-9f21-538e5c54cc97
-- title:
--   Functionals in the span of coordinate functionals vanish on all but finitely many unit vectors
-- statement:
--   Let $\iota$ be a set and let $\mathcal{T}$ be a *segment system* on $\iota$: a distinguished collection of finite subsets of $\iota$, called *segments*, which contains every singleton $\{v\}$, $v\in\iota$ (nothing is assumed about the empty set). For a finitely supported function $u:\iota\to\mathbb{R}$, its *segment norm* is
--   $$
--   \|u\|_{\mathcal{T}}=\sup\Big\{\Big(\sum_{k=1}^{n}\Big(\sum_{v\in S_k}u(v)\Big)^2\Big)^{1/2}\ :\ n\in\mathbb{N},\ S_1,\dots,S_n\ \text{pairwise disjoint segments}\Big\}.
--   $$
--
--   Let $X_{\mathcal{T}}$ be the Banach space completion of the space of finitely supported functions $\iota\to\mathbb{R}$ under this norm, and let $X_{\mathcal{T}}^*$ be its continuous dual with the operator norm $\|x\|=\sup_{\|z\|\le1}|x(z)|$. For $v\in\iota$ let $e_v\in X_{\mathcal{T}}$ be the image of the indicator function of $\{v\}$, and let $e_v^*\in X_{\mathcal{T}}^*$ be the coordinate functional, the continuous extension of $u\mapsto u(v)$ (it has norm at most $1$ because singletons are segments). For a finite set $S\subseteq\iota$ the *segment functional* is $\sigma_S=\sum_{v\in S}e_v^*$, so that $\sigma_S(u)=\sum_{v\in S}u(v)$ for finitely supported $u$.
--
--   Let $x\in X_{\mathcal{T}}^*$ lie in the linear span of the coordinate functionals $\{e_v^*:v\in\iota\}$ (finite linear combinations, without taking a closure). Then there is a finite set $S\subseteq\iota$ such that
--   $$
--   x(e_v)=0\qquad\text{for every } v\in\iota\setminus S .
--   $$
--
--   The norm closure of this span is the coordinate predual inside $X_{\mathcal{T}}^*$; for the tree of all finite words of natural numbers under the prefix order it is one of the two spaces in the distortion lower bound for diamond graphs that is the goal of this development. The lemma records the finite-support property of the dense subspace of finite combinations, a starting point for approximation arguments in the closure.
--
--   **Formalization Note** The span is Mathlib's `Submodule.span` of the range of `T.coordinate`, whose topological closure is `T.CoordinatePredual`; $e_v$ is `T.unitVector v`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/DiamondDistortion/SegmentNorm.lean#L1083-L1105

import Mathlib
import Definitions.Def_DiamondDistortion
import Definitions.Def_OAI_Analysis_DiamondDistortion_SegmentNorm

open OAI OAI.DiamondDistortion OAI.DiamondDistortion.SegmentSystem
universe u v
open scoped BigOperators Classical Topology
open Set
variable {ι : Type*} (T : SegmentSystem ι)
variable {T}
variable (T)
variable {T}
variable (T)

theorem OAI.DiamondDistortion.SegmentSystem.span_coordinates_finite_support {x : T.Dual}
    (hx : x ∈ Submodule.span ℝ (Set.range T.coordinate)) :
    ∃ S : Finset ι, ∀ v, v ∉ S → x (T.unitVector v)=0 := by sorry
