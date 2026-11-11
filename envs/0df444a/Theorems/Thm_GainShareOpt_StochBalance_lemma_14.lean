-- Prove2me | Theorems.Thm_GainShareOpt_StochBalance_lemma_14
-- name    : GainShareOpt.StochBalance.lemma_14
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T03:48:20.101192+00:00
-- url     : https://prove2.me/theorems/5cde583f-a702-4c5f-9579-8fef19ec9c91
-- title:
--   Lemma 14 — regularity of the decreasing flat branch of $y_\alpha$, (77)–(79)
-- statement:
--   Let $\alpha\in(1/e,1)$ and $y=y_\alpha$.
--   1. $y$ is locally Lipschitz on $[0,1)$.
--   2. On any interval in $[0,1)$ where $y(t)<e^{-t}$, $y$ is non-increasing; it is strictly decreasing on every such interval where also $y>1/e$.
--   3. Suppose $b\in(0,1]$ and $1/e<y(t)<e^{-t}$ for $0\le t<b$. Then $y\in C^1([0,b))$, and for every $t\in[0,b)$ there is a unique minimizer $\ell_\alpha(t)$ of $s\mapsto H_y(t,s)$ on $[0,t]$, with $\ell_\alpha(0)=0$ and $0<\ell_\alpha(t)<t$ for $t>0$, such that
--   $$y(t)=e^{-\ell_\alpha(t)}y(\ell_\alpha(t)),\qquad \min_{0\le s\le t}H_y(t,s)=\alpha,\qquad \frac{dy(t)}{dt}=\frac{y(t)-e^{-t}}{1-t+\ell_\alpha(t)}. \tag{77–79}$$
--   4. If $b<1$, these identities extend to $t=b$, and $y$ restricted to $[0,b]$ is $C^1$, with the left derivative at $b$.
--
--   It supplies the shooting system satisfied by the optimal trajectory.
--
--   Differences from the source:
--   - encoding: locally Lipschitz on [0, 1) → Lipschitz on [0, η] for every η ∈ (0, 1); reason: equivalent on [0, 1)
--   - encoding: on any interval where … → on every order-connected subset of [0, 1) where …; reason: an order-connected subset of ℝ is an interval
--   - encoding: y_α ∈ C¹([0, b)) and, for b < 1, the restriction to [0, b] is C¹ with the left derivative at b → ContDiffOn ℝ 1 on D = [0, b) and, if b < 1, on D = [0, b]; (79) as HasDerivWithinAt relative to D; reason: derivatives within the interval are one-sided at its endpoints, as the source specifies
--   - encoding: unique minimizing load ℓ_α(t) → a function ℓα with ℓα t ∈ [0, t] minimizing s ↦ H_y(t, s) on [0, t], every minimizer equal to ℓα t; reason: the source's ℓ_α is this pointwise-unique minimizer
--   - encoding: min_{0≤s≤t} H_{y_α}(t, s) = α → IsLeast of the image of [0, t] under s ↦ H_y(t, s) with value α; reason: states attainment and value
-- source:
--   Pan Xu, Gain-Sharing Optimization in Randomized Primal–Dual Analysis: Structure and Certification, arXiv:2503.09508 (held copy of 2026-10-31, sha256 d28f3b77…6c70b), p. 51, Lemma 14, (77)–(79)

import Mathlib
import Definitions.Def_GainShareOpt_StochBalance_Normalized
import Definitions.Def_GainShareOpt_StochBalance_Volterra

namespace GainShareOpt.StochBalance

/-- Lemma 14 (regularity of the decreasing flat branch of `y_α`). -/
theorem lemma_14 (α : ℝ) (hα : α ∈ Set.Ioo (Real.exp (-1)) 1) :
    (∀ η ∈ Set.Ioo (0 : ℝ) 1, ∃ K : NNReal, LipschitzOnWith K (fixedProfile α) (Set.Icc 0 η)) ∧
    (∀ I : Set ℝ, I.OrdConnected → I ⊆ Set.Ico 0 1 →
      (∀ t ∈ I, fixedProfile α t < Real.exp (-t)) → AntitoneOn (fixedProfile α) I) ∧
    (∀ I : Set ℝ, I.OrdConnected → I ⊆ Set.Ico 0 1 →
      (∀ t ∈ I, Real.exp (-1) < fixedProfile α t ∧ fixedProfile α t < Real.exp (-t)) →
      StrictAntiOn (fixedProfile α) I) ∧
    (∀ b ∈ Set.Ioc (0 : ℝ) 1,
      (∀ t ∈ Set.Ico 0 b, Real.exp (-1) < fixedProfile α t ∧ fixedProfile α t < Real.exp (-t)) →
      ∃ ℓα : ℝ → ℝ, ℓα 0 = 0 ∧
        ∀ D : Set ℝ, (D = Set.Ico 0 b ∨ (b < 1 ∧ D = Set.Icc 0 b)) →
          ContDiffOn ℝ 1 (fixedProfile α) D ∧
          ∀ t ∈ D,
            ℓα t ∈ Set.Icc 0 t ∧ (0 < t → 0 < ℓα t ∧ ℓα t < t) ∧
            (∀ s ∈ Set.Icc 0 t, testH (fixedProfile α) t (ℓα t) ≤ testH (fixedProfile α) t s) ∧
            (∀ s ∈ Set.Icc 0 t,
              (∀ s' ∈ Set.Icc 0 t, testH (fixedProfile α) t s ≤ testH (fixedProfile α) t s') →
              s = ℓα t) ∧
            fixedProfile α t = Real.exp (-(ℓα t)) * fixedProfile α (ℓα t) ∧
            IsLeast (testH (fixedProfile α) t '' Set.Icc 0 t) α ∧
            HasDerivWithinAt (fixedProfile α)
              ((fixedProfile α t - Real.exp (-t)) / (1 - t + ℓα t)) D t) := by sorry

end GainShareOpt.StochBalance
