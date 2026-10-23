-- Prove2me | Theorems.Thm_HerdingForecast_Equilibrium_theorem_1
-- name    : HerdingForecast.Equilibrium.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T23:09:02.853697+00:00
-- url     : https://prove2.me/theorems/db092015-a961-48e4-8e72-069cef658326
-- title:
--   Theorem 1, p. 12 (true part, 0 ≤ r < 1) — the normal forecast (10)–(11) is an equilibrium; equilibrium means are unique; the profile is unique among polynomially bounded variances
-- statement:
--   Consider $K \ge 2$ experts with the public signal (1) and private signals (2), precisions $\tau_x, \tau_y > 0$, the flat prior, and herding level $0 \le r < 1$, playing the game (9) with the logarithmic score (7) and the average KL deviation (8). Then:
--
--   1. **Existence.** The profile in which every expert $k \in \{1, \dots, K\}$ reports the normal distribution with mean
--   $$\mu_k = \mu^{MS}_k = \frac{(1-r)\tau_x}{(1-r)\tau_x+\tau_y}x_k + \frac{\tau_y}{(1-r)\tau_x+\tau_y}y \tag{10}$$
--   and variance
--   $$\sigma^2_k = a(x_k-y)^2 + d,\qquad a = \frac{r(1-r)\tau_x^2\tau_y^2}{[(\tau_x+\tau_y)^2 - r\tau_x^2][(1-r)\tau_x+\tau_y]^2},\quad d = \frac{(1+r)\tau_x+\tau_y}{(\tau_x+\tau_y)^2 - r\tau_x^2} \tag{11}$$
--   is a Bayesian Nash equilibrium.
--   2. **Uniqueness of the means.** In every equilibrium, every expert reports the mean (10) at every signal pair.
--   3. **Uniqueness of the profile under polynomial growth.** Every equilibrium whose reported variances grow at most polynomially in the private signal is the profile (10)–(11).
--
--   This is the paper's main characterization of herding in probabilistic forecasts: herding shifts the mean toward the public signal exactly as in Morris and Shin (2002), and inflates the variance by a term quadratic in the distance between the private and public signals.
--
--   **Formalization Note** The paper states that (10)–(11) is *the unique* equilibrium for $r \in [0,1]$. As printed this is false. At $r = 1$ every constant profile is an equilibrium, so $r < 1$ is assumed. At $r = \alpha = \tau_x/(\tau_x+\tau_y)$ the profile with means (10) and variances $a(x_k-y)^2 + d + c\,e^{\gamma(x_k-y)^2}$, $c > 0$, $\gamma = (1-\alpha^2)/(2(\hat\sigma^2_\theta + \tau_x^{-1}))$, is a second admissible equilibrium (e.g. $\tau_x = \tau_y = 1$, $r = 1/2$). The statement therefore keeps uniqueness of the means over all equilibria and uniqueness of the whole profile among equilibria with polynomially bounded variances. An equilibrium is an admissible profile (measurable, positive variances, the integrability making (9) finite) that is a best response at every signal pair; profiles are not restricted to be symmetric, linear or continuous. The paper restricts attention to symmetric equilibria (§2.2, p. 10), so its uniqueness claim is among symmetric profiles; the uniqueness clauses here range over all admissible profiles, which contains that case.
-- source:
--   Jia, Keppo & Satopää, Herding in Probabilistic Forecasts, SSRN 3674961 (PDF sha256 820fb50d…), p. 12, Theorem 1

import Mathlib
import Definitions.Def_HerdingForecast_Equilibrium_Model

namespace HerdingForecast.Equilibrium
theorem theorem_1 (P : Params) (hP : Standing P) :
    IsEquilibrium P (closedForm P) ∧
      (∀ s : Profile P.K, IsEquilibrium P s → ∀ (k : Fin P.K) (x y : ℝ), (s k x y).1 = muMS P x y) ∧
      (∀ s : Profile P.K, IsEquilibrium P s → PolyGrowth s → s = closedForm P) := by sorry
end HerdingForecast.Equilibrium
