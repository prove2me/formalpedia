-- Prove2me | Theorems.Thm_OAI_DiamondDistortion_FiniteAverage_jensen_sq
-- name    : OAI.DiamondDistortion.FiniteAverage.jensen_sq
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T00:36:01.38676+00:00
-- url     : https://prove2.me/theorems/721c6d5c-361f-4da4-8038-a86aa3c88d19
-- title:
--   Jensen's inequality for the square under finite probability weights
-- statement:
--   Let $\Omega$ be a finite set and let $w:\Omega\to\mathbb{R}$ be probability weights: $w(\omega)\ge0$ for every $\omega\in\Omega$ and $\sum_{\omega\in\Omega}w(\omega)=1$. Then for every function $f:\Omega\to\mathbb{R}$,
--   $$
--   \Big(\sum_{\omega\in\Omega}w(\omega)f(\omega)\Big)^2\le\sum_{\omega\in\Omega}w(\omega)f(\omega)^2 .
--   $$
--
--   In probabilistic language, $(\mathbb{E}f)^2\le\mathbb{E}f^2$ for every random variable on a finite probability space, i.e. variances are nonnegative. It is the basic convexity estimate behind the averaged energy bounds over finite laws used later.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/DiamondDistortion/FiniteAverage.lean#L16-L33

import Mathlib
import Definitions.Def_DiamondDistortion

open OAI OAI.DiamondDistortion
universe u v
open scoped BigOperators Classical Topology
open Set
variable {Ω : Type*} [Fintype Ω]

theorem OAI.DiamondDistortion.FiniteAverage.jensen_sq (w f : Ω → ℝ) (hw : ∀ ω, 0 ≤ w ω) (hs : ∑ ω, w ω = 1) :
    (∑ ω, w ω * f ω) ^ 2 ≤ ∑ ω, w ω * f ω ^ 2 := by sorry
