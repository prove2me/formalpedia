-- Prove2me | Theorems.Thm_OAI_DiamondDistortion_SegmentSystem_coefficientBall_convex
-- name    : OAI.DiamondDistortion.SegmentSystem.coefficientBall_convex
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T00:41:49.077993+00:00
-- url     : https://prove2.me/theorems/acdae1fa-b14b-4ebe-b0fd-02da41b3472b
-- title:
--   Convexity of the $\ell_1$-of-Euclidean coefficient ball over local segment families
-- statement:
--   Let $\iota$ be a set and let $\mathcal{T}$ be a *segment system* on $\iota$: a distinguished collection of finite subsets of $\iota$, called *segments*, which contains every singleton. Fix a finite set $K\subseteq\iota$. A *local family* on $K$ is a set $\mathcal{F}$ of pairwise disjoint segments contained in $K$; there are only finitely many local families, since each is a set of subsets of $K$. The coefficient space is the finite product $\mathcal{C}_K=\prod_{\mathcal{F}}\mathbb{R}^{\mathcal{F}}$ over all local families on $K$, each factor carrying its Euclidean norm $\|\cdot\|_2$, and for $R\in\mathbb{R}$ the coefficient ball is
--   $$
--   B_K(R)=\Big\{c\in\mathcal{C}_K:\ \sum_{\mathcal{F}}\|c_{\mathcal{F}}\|_2\le R\Big\}.
--   $$
--
--   For every real $R$ the set $B_K(R)$ is convex:
--   $$
--   c,d\in B_K(R),\quad \lambda,\mu\ge0,\quad \lambda+\mu=1\ \Longrightarrow\ \lambda c+\mu d\in B_K(R).
--   $$
--
--   $B_K(R)$ is the ball of radius $R$ for the $\ell_1$-sum of the Euclidean block norms (empty when $R<0$). In the surrounding development a coefficient vector in this ball whose blocks reproduce the coordinates of a dual functional on $K$ is turned into a finite probability law of normalized block atoms, with the unused mass placed on the zero atom; convexity of the parameter set is one of the ingredients for working with such decompositions.
--
--   **Formalization Note** The coefficient space is `T.Coefficients K`, a dependent function type over the finite type `T.LocalFamily K` with values in Euclidean spaces, and the ball is `T.coefficientBall K R`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/DiamondDistortion/SegmentNorm.lean#L870-L886

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

theorem OAI.DiamondDistortion.SegmentSystem.coefficientBall_convex (K : Finset ι) (R : ℝ) :
    Convex ℝ (T.coefficientBall K R) := by sorry
