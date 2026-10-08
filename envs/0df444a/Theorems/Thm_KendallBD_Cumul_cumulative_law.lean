-- Prove2me | Theorems.Thm_KendallBD_Cumul_cumulative_law
-- name    : KendallBD.Cumul.cumulative_law
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T11:26:42.785984+00:00
-- url     : https://prove2.me/theorems/27c29262-f922-4084-bada-9366ab2d53e7
-- title:
--   §5, (50)–(53), p. 11 — for constant rates λ₀ ≤ μ₀, ψ(1, w, ∞) generates the law Q_M of the cumulative population M_∞
-- statement:
--   Consider a simple birth-and-death process with constant birth rate $\lambda_0 > 0$ and death rate $\mu_0 \ge \lambda_0$ (a transient process), started from one ancestor. Let $\psi(z, w, t)$ be the function (50),
--   $$\psi(z, w, t) = w\,\frac{\alpha(\beta - z) + \beta(z - \alpha)e^{-\lambda_0 w(\beta - \alpha)t}}{(\beta - z) + (z - \alpha)e^{-\lambda_0 w(\beta - \alpha)t}},$$
--   where $\alpha < \beta$ are the roots of $\lambda_0 w z^2 - (\lambda_0 + \mu_0) z + \mu_0 = 0$, and let
--   $$Q_M = \frac{\lambda_0 + \mu_0}{2\lambda_0}\,\frac{(2M)!}{2^{2M}(M!)^2}\,\frac{x^M}{2M - 1} \quad (M = 1, 2, 3, \dots), \qquad x = \frac{4\lambda_0\mu_0}{(\lambda_0 + \mu_0)^2},$$
--   with $Q_0 = 0$. Then:
--
--   1. for every $w \in (0, 1)$, $\psi$ solves the equation (31), $\partial\psi/\partial t = \{\lambda_0 w z^2 - (\lambda_0 + \mu_0) z + \mu_0\}\,\partial\psi/\partial z$, at every $z \in [0, 1]$ and $t \ge 0$, and satisfies the boundary condition (32), $\psi(z, w, 0) = zw$ for every real $z$;
--   2. for every $w \in (0, 1)$ the series $\sum_M Q_M w^M$ converges and
--   $$\lim_{t \to \infty}\psi(1, w, t) = \sum_{M = 1}^{\infty} Q_M w^M;$$
--   3. $Q_M \ge 0$ for every $M$ and $\sum_{M \ge 1} Q_M = 1$.
--
--   In words: the joint generating function of the population size and the cumulative population $M_t$ (the number of individuals ever alive) is (50), and the limiting distribution of $M_t$, read off $\psi(1, w, \infty)$, is the proper probability law $(Q_M)_{M \ge 1}$ of (52). For $\lambda_0 = \mu_0$ the law has an infinite mean; for $\lambda_0 < \mu_0$ its mean is $\mu_0/(\mu_0 - \lambda_0)$.
--
--   **Formalization Note.** The process and the joint law $P_{n,M}(t)$ are not constructed, as in the paper: "the law of $M_\infty$" is read, as on p. 11, as the coefficients of the generating function $\lim_{t\to\infty}\psi(1, w, t)$, and $\psi$ is tied to the process through the equation (31) and the boundary condition (32). The roots are used only for $0 < w < 1$, where $0 < \alpha < 1 < \beta$; this range determines the coefficients. $Q_0 = 0$ encodes $M_\infty \ge M_0 = 1$.
-- source:
--   Kendall, On the generalized "birth-and-death" process, Ann. Math. Statist. 19 (1948), §5, (50), (51), (52), (53), p. 11, with §4, (31)–(32), p. 8

import Mathlib
import Definitions.Def_KendallBD_Cumul_Setting
open Filter Topology

namespace KendallBD.Cumul

theorem cumulative_law (lam0 mu0 : ℝ) (hlam : 0 < lam0) (hle : lam0 ≤ mu0) :
    (∀ w ∈ Set.Ioo (0:ℝ) 1,
      (∀ z ∈ Set.Icc (0:ℝ) 1, ∀ t : ℝ, 0 ≤ t → SolvesPDE lam0 mu0 (psi lam0 mu0) z w t) ∧
      ∀ z : ℝ, psi lam0 mu0 z w 0 = z * w) ∧
    (∀ w ∈ Set.Ioo (0:ℝ) 1,
      Summable (fun M : ℕ => Q lam0 mu0 M * w ^ M) ∧
      Tendsto (fun t => psi lam0 mu0 1 w t) atTop (𝓝 (∑' M : ℕ, Q lam0 mu0 M * w ^ M))) ∧
    ((∀ M : ℕ, 0 ≤ Q lam0 mu0 M) ∧ HasSum (Q lam0 mu0) 1) := by sorry

end KendallBD.Cumul
