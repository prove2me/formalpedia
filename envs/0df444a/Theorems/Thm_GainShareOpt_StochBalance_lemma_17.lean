-- Prove2me | Theorems.Thm_GainShareOpt_StochBalance_lemma_17
-- name    : GainShareOpt.StochBalance.lemma_17
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T03:48:29.635038+00:00
-- url     : https://prove2.me/theorems/8ed008a4-401e-4221-9367-fd3653aa2e60
-- title:
--   Lemma 17 — stability near a feasible value; continuity of $q$
-- statement:
--   Let $\alpha>1/e$ be feasible for (73). For every $\beta\in(1/e,1)$ sufficiently close to $\alpha$, $y_\beta$ also reaches $1/e$ before time $1$ and before reaching $e^{-t}$; its constant extension $g_\beta$ lies in $G$ and satisfies all partial-load constraints $H_{g_\beta}(t,s)\ge\beta$, $0\le s\le t\le1$; and
--   $$q(\beta)=A(g_\beta)=\int_0^{\tau_\beta}e^{-z}(1-y_\beta(z))\,dz+(1-1/e)e^{-\tau_\beta}.$$
--   Moreover $q$ is continuous at $\alpha$. No feasibility of the scalar constraint at $\beta$ is assumed.
--
--   It is the perturbation step that forces the scalar constraint to be tight at the optimum.
--
--   Differences from the source:
--   - encoding: α > 1/e is feasible for (73) → 1/e < α and ∃ g, Feasible73 α g; reason: feasibility of a value means some g ∈ G satisfies the constraints at that value
--   - encoding: the decreasing branch of y reaches 1/e at a time τ before reaching e^{−t} → τ = hitTime (first t ∈ [0, 1) with y(t) = 1/e) lies in the stated interval, y(τ) = 1/e, y > 1/e on [0, τ), y(t) < e^{−t} on [0, τ]; reason: the first hitting time of 1/e is the τ of the source
--   - encoding: for every β sufficiently close to α → ∃ δ > 0 such that every β ∈ (1/e, 1) with |β − α| < δ; reason: definition of 'sufficiently close'
--   - encoding: q continuous at α → ContinuousAt returnValue α; reason: α ≤ 1 − 1/e < 1 by Lemma 12, so a neighbourhood of α lies in (1/e, 1)
-- source:
--   Pan Xu, Gain-Sharing Optimization in Randomized Primal–Dual Analysis: Structure and Certification, arXiv:2503.09508 (held copy of 2026-10-31, sha256 d28f3b77…6c70b), p. 55, Lemma 17

import Mathlib
import Definitions.Def_GainShareOpt_StochBalance_Normalized
import Definitions.Def_GainShareOpt_StochBalance_Volterra

namespace GainShareOpt.StochBalance

/-- Lemma 17 (stability near a feasible value). -/
theorem lemma_17 (α : ℝ) (hα : Real.exp (-1) < α) (hfeas : ∃ g, Feasible73 α g) :
    (∃ δ > 0, ∀ β ∈ Set.Ioo (Real.exp (-1)) 1, |β - α| < δ →
      hitTime β ∈ Set.Ioo (0 : ℝ) 1 ∧ fixedProfile β (hitTime β) = Real.exp (-1) ∧
      (∀ t ∈ Set.Ico 0 (hitTime β), Real.exp (-1) < fixedProfile β t) ∧
      (∀ t ∈ Set.Icc 0 (hitTime β), fixedProfile β t < Real.exp (-t)) ∧
      canonProfile β ∈ ClassG ∧
      (∀ t s : ℝ, 0 ≤ s → s ≤ t → t ≤ 1 → β ≤ testH (canonProfile β) t s) ∧
      returnValue β = (∫ z in (0 : ℝ)..(hitTime β), Real.exp (-z) * (1 - fixedProfile β z))
        + (1 - Real.exp (-1)) * Real.exp (-(hitTime β))) ∧
    ContinuousAt returnValue α := by sorry

end GainShareOpt.StochBalance
