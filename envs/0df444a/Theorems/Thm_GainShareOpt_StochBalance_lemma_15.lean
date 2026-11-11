-- Prove2me | Theorems.Thm_GainShareOpt_StochBalance_lemma_15
-- name    : GainShareOpt.StochBalance.lemma_15
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T03:48:19.625411+00:00
-- url     : https://prove2.me/theorems/0e953265-722c-4317-90fc-5c6fb40da5f8
-- title:
--   Lemma 15 — canonical profile $g_\alpha$ of a feasible value
-- statement:
--   Suppose $\alpha>1/e$ is feasible for (73). Then $y_\alpha$ reaches $1/e$ at a time $\tau_\alpha\in(0,1)$ while still below $e^{-t}$. The profile $g_\alpha=y_\alpha$ on $[0,\tau_\alpha]$, $g_\alpha=1/e$ on $[\tau_\alpha,1]$, lies in $G$ and satisfies
--   $$H_{g_\alpha}(t,s)\ge\alpha\ (0\le s\le t\le1),\qquad \min_{0\le s\le t}H_{g_\alpha}(t,s)=\alpha\ (0\le t\le\tau_\alpha). \tag{81–82}$$
--   For every feasible pair $(\alpha,g)$: $g_\alpha\le g$ and $A(g_\alpha)\ge A(g)\ge\alpha$. Moreover $g_\alpha=y_\alpha$ on $[0,1)$, $g_\alpha(t)<e^{-t}$ for $t<1$, and $g_\alpha$ restricted to $[0,\tau_\alpha]$ is $C^1$ with strictly negative derivative, one-sided at the endpoints.
--
--   $g_\alpha$ is the least feasible profile at level $\alpha$.
--
--   Differences from the source:
--   - encoding: α > 1/e is feasible for (73) → 1/e < α and ∃ g, Feasible73 α g; reason: feasibility of a value means some g ∈ G satisfies the constraints at that value
--   - encoding: the decreasing branch of y reaches 1/e at a time τ before reaching e^{−t} → τ = hitTime (first t ∈ [0, 1) with y(t) = 1/e) lies in the stated interval, y(τ) = 1/e, y > 1/e on [0, τ), y(t) < e^{−t} on [0, τ]; reason: the first hitting time of 1/e is the τ of the source
--   - encoding: g_α ≤ g → g_α(t) ≤ g(t) for t ∈ [0, 1]; reason: profiles of G live on [0, 1]
--   - encoding: restriction to [0, τ_α] is C¹ with strictly negative derivative, including one-sided derivatives at the endpoints → ContDiffOn ℝ 1 on [0, τ_α] and derivWithin on [0, τ_α] negative at every point; reason: derivWithin on a closed interval is the one-sided derivative at its endpoints
-- source:
--   Pan Xu, Gain-Sharing Optimization in Randomized Primal–Dual Analysis: Structure and Certification, arXiv:2503.09508 (held copy of 2026-10-31, sha256 d28f3b77…6c70b), p. 53, Lemma 15, (81)–(82)

import Mathlib
import Definitions.Def_GainShareOpt_StochBalance_Normalized
import Definitions.Def_GainShareOpt_StochBalance_Volterra

namespace GainShareOpt.StochBalance

/-- Lemma 15 (canonical profile of a feasible value). -/
theorem lemma_15 (α : ℝ) (hα : Real.exp (-1) < α) (hfeas : ∃ g, Feasible73 α g) :
    hitTime α ∈ Set.Ioo (0 : ℝ) 1 ∧ fixedProfile α (hitTime α) = Real.exp (-1) ∧
    (∀ t ∈ Set.Ico 0 (hitTime α), Real.exp (-1) < fixedProfile α t) ∧
    (∀ t ∈ Set.Icc 0 (hitTime α), fixedProfile α t < Real.exp (-t)) ∧
    canonProfile α ∈ ClassG ∧
    (∀ t s : ℝ, 0 ≤ s → s ≤ t → t ≤ 1 → α ≤ testH (canonProfile α) t s) ∧
    (∀ t ∈ Set.Icc 0 (hitTime α), IsLeast (testH (canonProfile α) t '' Set.Icc 0 t) α) ∧
    (∀ g : ℝ → ℝ, Feasible73 α g →
      (∀ t ∈ Set.Icc (0 : ℝ) 1, canonProfile α t ≤ g t) ∧
      scoreA g ≤ scoreA (canonProfile α) ∧ α ≤ scoreA g) ∧
    (∀ t ∈ Set.Ico (0 : ℝ) 1, canonProfile α t = fixedProfile α t) ∧
    (∀ t ∈ Set.Ico (0 : ℝ) 1, canonProfile α t < Real.exp (-t)) ∧
    ContDiffOn ℝ 1 (canonProfile α) (Set.Icc 0 (hitTime α)) ∧
    (∀ t ∈ Set.Icc 0 (hitTime α),
      derivWithin (canonProfile α) (Set.Icc 0 (hitTime α)) t < 0) := by sorry

end GainShareOpt.StochBalance
