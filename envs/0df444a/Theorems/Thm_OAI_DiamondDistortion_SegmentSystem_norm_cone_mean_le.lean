-- Prove2me | Theorems.Thm_OAI_DiamondDistortion_SegmentSystem_norm_cone_mean_le
-- name    : OAI.DiamondDistortion.SegmentSystem.norm_cone_mean_le
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T00:39:46.941544+00:00
-- url     : https://prove2.me/theorems/8faa4453-67f2-4219-b4db-3d5aeebe6eb4
-- title:
--   Dual norm bound for weighted averages of segment combinations over disjoint cones
-- statement:
--   Let $\iota$ be a set and let $\mathcal{T}$ be a *segment system* on $\iota$: a distinguished collection of finite subsets of $\iota$, called *segments*, which contains every singleton $\{v\}$, $v\in\iota$ (nothing is assumed about the empty set). For a finitely supported function $u:\iota\to\mathbb{R}$, its *segment norm* is
--   $$
--   \|u\|_{\mathcal{T}}=\sup\Big\{\Big(\sum_{k=1}^{n}\Big(\sum_{v\in S_k}u(v)\Big)^2\Big)^{1/2}\ :\ n\in\mathbb{N},\ S_1,\dots,S_n\ \text{pairwise disjoint segments}\Big\}.
--   $$
--
--   Let $X_{\mathcal{T}}$ be the Banach space completion of the space of finitely supported functions $\iota\to\mathbb{R}$ under this norm, and let $X_{\mathcal{T}}^*$ be its continuous dual with the operator norm $\|x\|=\sup_{\|z\|\le1}|x(z)|$. For $v\in\iota$ let $e_v\in X_{\mathcal{T}}$ be the image of the indicator function of $\{v\}$, and let $e_v^*\in X_{\mathcal{T}}^*$ be the coordinate functional, the continuous extension of $u\mapsto u(v)$ (it has norm at most $1$ because singletons are segments). For a finite set $S\subseteq\iota$ the *segment functional* is $\sigma_S=\sum_{v\in S}e_v^*$, so that $\sigma_S(u)=\sum_{v\in S}u(v)$ for finitely supported $u$.
--
--   Let $\Omega$ be a nonempty finite set and $\kappa$ a finite set. For $\omega\in\Omega$ and $g\in\kappa$ let $S_\omega(g)\subseteq\iota$ be a finite set and $a_\omega(g)\in\mathbb{R}$, and let $w:\Omega\to\mathbb{R}$ satisfy $w(\omega)\ge0$ for all $\omega$. Assume that every nonempty $S_\omega(g)$ is a segment, and that sets carrying different labels are disjoint: $S_\omega(g)\cap S_\nu(h)=\emptyset$ whenever $g\neq h$, for all $\omega,\nu\in\Omega$. Then
--   $$
--   \Big\|\sum_{\omega\in\Omega}w(\omega)\sum_{g\in\kappa}a_\omega(g)\,\sigma_{S_\omega(g)}\Big\|_{X_{\mathcal{T}}^*}\le\Big(\sum_{g\in\kappa}\Big(\sum_{\omega\in\Omega}w(\omega)\,|a_\omega(g)|\Big)^2\Big)^{1/2}.
--   $$
--
--   For a fixed label $g$ the sets $S_\omega(g)$, $\omega\in\Omega$, form a "cone" of possibly overlapping segments, while cones with different labels are disjoint. The estimate bounds the norm of a weighted average of the represented functionals $\sum_g a_\omega(g)\sigma_{S_\omega(g)}$ by the Euclidean norm of the pooled absolute coefficients, label by label; when $w$ is a probability vector it bounds the barycentre of a finite law of such functionals. The weights are not required to sum to one.
--
--   **Formalization Note** For each outcome $\omega$ the inner sum over $g$ is `T.combine` applied to the families $S_\omega$ and $a_\omega$, and $X_{\mathcal{T}}^*$ is `T.Dual`. The nonemptiness of $\Omega$ is an explicit hypothesis of the Lean statement.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/DiamondDistortion/SegmentNorm.lean#L522-L576

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

theorem OAI.DiamondDistortion.SegmentSystem.norm_cone_mean_le {Ω κ : Type*} [Fintype Ω] [Nonempty Ω] [Fintype κ]
    (S : Ω → κ → Finset ι) (a : Ω → κ → ℝ) (w : Ω → ℝ) (hw : ∀ ω, 0 ≤ w ω)
    (hS : ∀ ω g, (S ω g).Nonempty → T.IsSegment (S ω g))
    (hd : ∀ g h, g ≠ h → ∀ ω ν, Disjoint (S ω g) (S ν h)) :
    ‖∑ ω, w ω • T.combine (S ω) (a ω)‖ ≤
      Real.sqrt (∑ g, (∑ ω, w ω * |a ω g|) ^ 2) := by sorry
