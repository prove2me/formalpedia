-- Prove2me | Theorems.Thm_GainShareOpt_StochBalance_lemma_13
-- name    : GainShareOpt.StochBalance.lemma_13
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T03:48:23.957256+00:00
-- url     : https://prove2.me/theorems/8089539b-9c3d-466a-978d-c0c94c960801
-- title:
--   Lemma 13 — Volterra fixed point $y_\alpha$: existence, uniqueness, comparison, parameter continuity (76)
-- statement:
--   Let $\alpha\in(1/e,1)$. There is a unique continuous $y_\alpha:[0,1)\to\mathbb R$ whose restriction to each $[0,\eta]$, $\eta<1$, is a fixed point of $T_\alpha$ (75). It satisfies $y_\alpha(0)=\alpha$ and $y_\alpha\ge1/e$. If $0<\eta<1$ and $g$ is continuous on $[0,\eta]$ with $g\ge T_\alpha g$ there, then $g\ge y_\alpha$ on $[0,\eta]$. For $\alpha,\beta\in(1/e,1)$ and $0<\eta<1$,
--   $$\|y_\alpha-y_\beta\|_{\infty,[0,\eta]}\le\frac{\exp(\eta/(1-\eta))}{1-\eta}\,|\alpha-\beta|. \tag{76}$$
--   Finally $y_\alpha\le y_\beta$ whenever $1/e<\alpha\le\beta<1$.
--
--   This comparison principle is the engine of the attainment proof (Theorem 7) and of the validated enclosure.
--
--   Differences from the source:
--   - encoding: unique continuous y_α : [0, 1) → ℝ, fixed point on each [0, η] → IsFixedProfile α (continuous on [0, 1), T_α y = y pointwise on [0, 1)); fixedProfile α satisfies it; any two such functions agree on [0, 1); reason: T_α y (t) depends only on y on [0, t], so a fixed point on every [0, η], η < 1, is a pointwise fixed point on [0, 1); functions are ℝ → ℝ
--   - encoding: inner max over 0 ≤ s ≤ t in (75) → sSup of the image of [0, t]; reason: a maximum of a continuous function on a compact set
--   - encoding: g ∈ C([0, η]), η < 1 → g : ℝ → ℝ continuous on [0, η], 0 < η < 1; reason: T_α is defined for 0 < η < 1 (p. 50)
--   - encoding: ‖y_α − y_β‖_{∞,[0,η]} ≤ C |α − β| → |y_α(t) − y_β(t)| ≤ C |α − β| for all t ∈ [0, η], for every η ∈ (0, 1); reason: a sup-norm bound is a pointwise bound
-- source:
--   Pan Xu, Gain-Sharing Optimization in Randomized Primal–Dual Analysis: Structure and Certification, arXiv:2503.09508 (held copy of 2026-10-31, sha256 d28f3b77…6c70b), p. 50, Lemma 13, (75)–(76)

import Mathlib
import Definitions.Def_GainShareOpt_StochBalance_Normalized
import Definitions.Def_GainShareOpt_StochBalance_Volterra

namespace GainShareOpt.StochBalance

/-- Lemma 13: for `α ∈ (1/e, 1)`, the fixed point `y_α` of (75) on `[0, 1)` exists and is unique,
`y_α(0) = α`, `y_α ≥ 1/e`, it lies below every continuous supersolution on `[0, η]`, it depends
Lipschitz-continuously on `α` as in (76), and it is non-decreasing in `α`. -/
theorem lemma_13 (α : ℝ) (hα : α ∈ Set.Ioo (Real.exp (-1)) 1) :
    IsFixedProfile α (fixedProfile α) ∧
    (∀ y₁ y₂ : ℝ → ℝ, IsFixedProfile α y₁ → IsFixedProfile α y₂ →
      ∀ t ∈ Set.Ico (0 : ℝ) 1, y₁ t = y₂ t) ∧
    fixedProfile α 0 = α ∧
    (∀ t ∈ Set.Ico (0 : ℝ) 1, Real.exp (-1) ≤ fixedProfile α t) ∧
    (∀ η ∈ Set.Ioo (0 : ℝ) 1, ∀ g : ℝ → ℝ, ContinuousOn g (Set.Icc 0 η) →
      (∀ t ∈ Set.Icc 0 η, volterraOp α g t ≤ g t) →
      ∀ t ∈ Set.Icc 0 η, fixedProfile α t ≤ g t) ∧
    (∀ β ∈ Set.Ioo (Real.exp (-1)) 1, ∀ η ∈ Set.Ioo (0 : ℝ) 1, ∀ t ∈ Set.Icc 0 η,
      |fixedProfile α t - fixedProfile β t| ≤ Real.exp (η / (1 - η)) / (1 - η) * |α - β|) ∧
    (∀ β : ℝ, α ≤ β → β < 1 → ∀ t ∈ Set.Ico (0 : ℝ) 1, fixedProfile α t ≤ fixedProfile β t) := by sorry

end GainShareOpt.StochBalance
