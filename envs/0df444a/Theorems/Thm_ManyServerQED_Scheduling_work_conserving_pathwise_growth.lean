-- Prove2me | Theorems.Thm_ManyServerQED_Scheduling_work_conserving_pathwise_growth
-- name    : ManyServerQED.Scheduling.work_conserving_pathwise_growth
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-25T18:16:37.093018+00:00
-- url     : https://prove2.me/theorems/1bf37ad3-34ae-43c8-a603-27467668d47e
-- title:
--   A pathwise polynomial growth bound for the work-conserving queue drift
-- statement:
--   Let $x,w,q$ be integrable vector-valued paths on every subinterval $[0,t]$ of $[0,T]$. The nonnegative queue $q$ has total mass equal to the positive part of the total state. Suppose
--   $$x_i(t)=w_i(t)+\int_0^t\big((\mu_i-\theta_i)q_i(s)-\mu_i x_i(s)ig)\,ds,$$
--   where $0<\mu_i\le a$, $0\le\theta_i\le a$, and $a>0$. If $\|w(t)\|_1\le B$ throughout the horizon, then throughout the same horizon
--   $$\|x(t)\|_1\le k(1+aT)^2 B.$$
--   Here $k$ is the number of classes. This is a deterministic polynomial-in-horizon bound for both the diffusion-scale queue equation and the limiting diffusion when they are driven by an additive input.
-- source:
--   Atar, Mandelbaum and Reiman (2004), https://arxiv.org/abs/math/0407058, Proposition 4(ii), equations (33)–(40), pp. 23–25, and the bound (52) in Lemma 3, p. 32. Deterministic finite-horizon sup-norm version.

import Definitions.Def_ManyServerQED_Scheduling_Diffusion

open MeasureTheory Set

namespace ManyServerQED.Scheduling

theorem work_conserving_pathwise_growth {k : ℕ} (μ θ : Fin k → ℝ) (a : ℝ) (ha : 0 < a)
    (hμ : ∀ i, 0 < μ i) (hμa : ∀ i, μ i ≤ a) (hθ : ∀ i, 0 ≤ θ i) (hθa : ∀ i, θ i ≤ a)
    (x w q : ℝ → Fin k → ℝ) (T B : ℝ) (hT : 0 ≤ T) (hB : 0 ≤ B)
    (hint : ∀ t ∈ Icc 0 T, ∀ i,
      IntervalIntegrable (fun s => x s i) volume 0 t ∧
      IntervalIntegrable (fun s => w s i) volume 0 t ∧
      IntervalIntegrable (fun s => q s i) volume 0 t)
    (hqn : ∀ t ∈ Icc 0 T, ∀ i, 0 ≤ q t i)
    (hq : ∀ t ∈ Icc 0 T, (∑ i, q t i) = max (∑ i, x t i) 0)
    (hw : ∀ t ∈ Icc 0 T, l1norm (w t) ≤ B)
    (hEq : ∀ t ∈ Icc 0 T, ∀ i, x t i = w t i +
      ∫ s in (0 : ℝ)..t, ((μ i - θ i) * q s i - μ i * x s i)) :
    ∀ t ∈ Icc 0 T, l1norm (x t) ≤ (k : ℝ) * (1 + a * T) ^ 2 * B := by sorry

end ManyServerQED.Scheduling
