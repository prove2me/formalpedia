-- Prove2me | Theorems.Thm_HerdingForecast_Equilibrium_ec_11_12_best_response
-- name    : HerdingForecast.Equilibrium.ec_11_12_best_response
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T23:08:56.550001+00:00
-- url     : https://prove2.me/theorems/7eb322d3-91f8-4c39-8008-be81d88fd8ac
-- title:
--   (EC.11)–(EC.12), p. ec41 (PDF 79) — against admissible opponents, the unique best response is the first-order-condition forecast
-- statement:
--   Assume $K \ge 2$, $\tau_x, \tau_y > 0$ and $0 \le r < 1$. Let $s$ be an admissible strategy profile, $k$ an expert and $(x_k, y)$ a signal pair. Define
--   $$\mu^* = (1-r)\hat\theta_k + r\,\frac{1}{K-1}\sum_{j\ne k}\mathbb E[\mu_j \mid x_k, y],$$
--   $$v^* = (1-r)\big((\mu^*-\hat\theta_k)^2 + \hat\sigma^2_\theta\big) + r\,\frac{1}{K-1}\sum_{j\ne k}\mathbb E\big[(\mu^*-\mu_j)^2 + \sigma_j^2 \mid x_k, y\big],$$
--   where $(\mu_j, \sigma_j^2) = s_j(x_j, y)$ and $x_j$ follows the predictive law given $(x_k, y)$. Then $v^* > 0$, and for every forecast $a = (\mu, \sigma^2)$ with $\sigma^2 > 0$ and $a \ne (\mu^*, v^*)$, the objective (9) of expert $k$ at $(x_k, y)$ is strictly larger at $a$ than at $(\mu^*, v^*)$.
--
--   So the first-order conditions (EC.11)–(EC.12) characterize best responses exactly: a profile is an equilibrium if and only if it is admissible and solves them at every signal pair.
--
--   **Formalization Note** The paper derives (EC.11)–(EC.12) from first-order conditions after asserting that the payoff is convex; the objective is not jointly convex in $(\mu, \sigma^2)$, so the statement here is the unique-minimizer property that the derivation needs. In (EC.11) the paper writes $\hat\theta_i$ for $\hat\theta_k$.
-- source:
--   Jia, Keppo & Satopää, Herding in Probabilistic Forecasts, SSRN 3674961 (PDF sha256 820fb50d…), p. ec41 (PDF 79), EC.5.1, (EC.11)–(EC.12)

import Mathlib
import Definitions.Def_HerdingForecast_Equilibrium_Model

namespace HerdingForecast.Equilibrium
theorem ec_11_12_best_response (P : Params) (hP : Standing P) (s : Profile P.K)
    (hs : Admissible P s) (k : Fin P.K) (x y : ℝ) :
    0 < brVar P s k x y ∧
      ∀ a : ℝ × ℝ, 0 < a.2 → a ≠ (brMean P s k x y, brVar P s k x y) →
        objective P s k x y (brMean P s k x y, brVar P s k x y) < objective P s k x y a := by sorry
end HerdingForecast.Equilibrium
