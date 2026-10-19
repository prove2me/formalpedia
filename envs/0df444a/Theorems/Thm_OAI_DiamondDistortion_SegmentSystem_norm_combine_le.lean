-- Prove2me | Theorems.Thm_OAI_DiamondDistortion_SegmentSystem_norm_combine_le
-- name    : OAI.DiamondDistortion.SegmentSystem.norm_combine_le
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T00:38:55.515192+00:00
-- url     : https://prove2.me/theorems/a65d41cf-9379-44a3-a169-d687331b22f7
-- title:
--   Disjoint segment combinations have dual norm at most the Euclidean norm of their coefficients
-- statement:
--   Let $\iota$ be a set and let $\mathcal{T}$ be a *segment system* on $\iota$: a distinguished collection of finite subsets of $\iota$, called *segments*, which contains every singleton $\{v\}$, $v\in\iota$ (nothing is assumed about the empty set). For a finitely supported function $u:\iota\to\mathbb{R}$, its *segment norm* is
--   $$
--   \|u\|_{\mathcal{T}}=\sup\Big\{\Big(\sum_{k=1}^{n}\Big(\sum_{v\in S_k}u(v)\Big)^2\Big)^{1/2}\ :\ n\in\mathbb{N},\ S_1,\dots,S_n\ \text{pairwise disjoint segments}\Big\}.
--   $$
--
--   Let $X_{\mathcal{T}}$ be the Banach space completion of the space of finitely supported functions $\iota\to\mathbb{R}$ under this norm, and let $X_{\mathcal{T}}^*$ be its continuous dual with the operator norm $\|x\|=\sup_{\|z\|\le1}|x(z)|$. For $v\in\iota$ let $e_v\in X_{\mathcal{T}}$ be the image of the indicator function of $\{v\}$, and let $e_v^*\in X_{\mathcal{T}}^*$ be the coordinate functional, the continuous extension of $u\mapsto u(v)$ (it has norm at most $1$ because singletons are segments). For a finite set $S\subseteq\iota$ the *segment functional* is $\sigma_S=\sum_{v\in S}e_v^*$, so that $\sigma_S(u)=\sum_{v\in S}u(v)$ for finitely supported $u$.
--
--   Let $\kappa$ be a finite index set, let $(S_g)_{g\in\kappa}$ be pairwise disjoint finite subsets of $\iota$ such that every nonempty $S_g$ is a segment, and let $a=(a_g)_{g\in\kappa}\in\mathbb{R}^\kappa$. Then
--   $$
--   \Big\|\sum_{g\in\kappa}a_g\,\sigma_{S_g}\Big\|_{X_{\mathcal{T}}^*}\le\Big(\sum_{g\in\kappa}a_g^2\Big)^{1/2}.
--   $$
--
--   This is the Cauchy–Schwarz estimate dual to the definition of the segment norm: a functional represented by a disjoint segment family with coefficient vector $a$ lies in the ball of radius $\|a\|_2$ of $X_{\mathcal{T}}^*$. Empty pieces are permitted, so the bound survives after the segments are restricted to a subset.
--
--   **Formalization Note** The functional $\sum_g a_g\sigma_{S_g}$ is `T.combine S a`, and $X_{\mathcal{T}}^*$ is `T.Dual`, the full continuous dual of the completion `T.JamesSpace`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/DiamondDistortion/SegmentNorm.lean#L496-L520

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

theorem OAI.DiamondDistortion.SegmentSystem.norm_combine_le {κ : Type*} [Fintype κ] (S : κ → Finset ι) (a : κ → ℝ)
    (hS : ∀ i, (S i).Nonempty → T.IsSegment (S i))
    (hd : Pairwise (fun i j => Disjoint (S i) (S j))) :
    ‖T.combine S a‖ ≤ Real.sqrt (∑ i, (a i) ^ 2) := by sorry
