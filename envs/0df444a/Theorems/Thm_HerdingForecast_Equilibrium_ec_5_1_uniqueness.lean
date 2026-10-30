-- Prove2me | Theorems.Thm_HerdingForecast_Equilibrium_ec_5_1_uniqueness
-- name    : HerdingForecast.Equilibrium.ec_5_1_uniqueness
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T23:08:58.855634+00:00
-- url     : https://prove2.me/theorems/adfebe54-8124-4e25-8cd4-6a515c3b1866
-- title:
--   EC.5.1, p. ec42 (PDF 80) — solutions of (EC.11)–(EC.12) have the means (10), and are the closed form under polynomial growth (unique as printed only with it)
-- statement:
--   Assume $K \ge 2$, $\tau_x, \tau_y > 0$ and $0 \le r < 1$. Let $s$ be an admissible profile that solves the first-order conditions (EC.11)–(EC.12) at every expert $k$ and every signal pair $(x_k, y)$. Then:
--
--   1. every expert reports the Morris–Shin mean (10): $\mu_k(x_k, y) = \mu^{MS}_k$ for all $k, x_k, y$;
--   2. if moreover the reported variances grow at most polynomially in the private signal (for each $k$ and $y$ there are $C, N$ with $\sigma_k^2(x, y) \le C(1+|x|^N)$), then $s$ is the closed-form profile: $\sigma^2_k = a(x_k-y)^2 + d$ as in (11).
--
--   This is the uniqueness half of Theorem 1, which the paper derives by the iterated-expectation argument of Morris and Shin (2002).
--
--   **Formalization Note** The growth bound in item 2 is not in the paper, and it cannot be dropped: with $\alpha = \tau_x/(\tau_x+\tau_y)$, $\hat\sigma^2_{x_{-i}} = \hat\sigma^2_\theta + \tau_x^{-1}$ and $\gamma = (1-\alpha^2)/(2\hat\sigma^2_{x_{-i}})$, at $r = \alpha$ the profile with means (10) and variances $a(x_k-y)^2 + d + c\,e^{\gamma(x_k-y)^2}$, $c > 0$, also solves (EC.11)–(EC.12) and is admissible (for instance $\tau_x = \tau_y = 1$, $r = 1/2$). The paper's remark that (EC.11) alone has the unique solution $\mu^{MS}$ is likewise false at $r = \alpha$ ($\mu^{MS} + c\,e^{\gamma(x_k-y)^2}$ solves it, with square-integrable means when $\alpha^2 > 1/2$), so item 1 uses both conditions.
-- source:
--   Jia, Keppo & Satopää, Herding in Probabilistic Forecasts, SSRN 3674961 (PDF sha256 820fb50d…), p. ec42 (PDF 80), EC.5.1 (uniqueness paragraph)

import Mathlib
import Definitions.Def_HerdingForecast_Equilibrium_Model

namespace HerdingForecast.Equilibrium
theorem ec_5_1_uniqueness (P : Params) (hP : Standing P) (s : Profile P.K)
    (hs : Admissible P s)
    (hfoc : ∀ (k : Fin P.K) (x y : ℝ), s k x y = (brMean P s k x y, brVar P s k x y)) :
    (∀ (k : Fin P.K) (x y : ℝ), (s k x y).1 = muMS P x y) ∧
      (PolyGrowth s → s = closedForm P) := by sorry
end HerdingForecast.Equilibrium
