-- Prove2me | Theorems.Thm_NetworkedMarkets_Relaxation_step_i_2_subscription_implementation
-- name    : NetworkedMarkets.Relaxation.step_i_2_subscription_implementation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T17:25:27.159503+00:00
-- url     : https://prove2.me/theorems/27a6b204-03d0-40c9-a0fc-617b0223114e
-- title:
--   Proof of Theorem 1, Step (i-2), pp. ec40–ec42 (PDF 84–86) — prices θ^s and subscriptions (EC.104) implement the optimum of (7) as a competitive equilibrium with revenue h(q̄^s, q̄^b)
-- statement:
--   Under the standing assumptions and Assumptions 1–2, let $(\bar x,\bar q^s,\bar q^b)$ be an optimal solution of (7) and let $(\theta^b,\theta^s,\eta^b,\eta^s,\pi)$ be a special dual multiplier vector for it, i.e. a solution of (EC.3). Set the prices $p_i:=\theta^s_i$ (EC.103), the commissions $\gamma=0$, and the subscription fees
--   $$\mu^s_i=\theta^s_i-F^{-1}_{s_i}\Big(\frac{\bar q^s_i}{s_i}\Big),\qquad \mu^b_j=F^{-1}_{b_j}\Big(1-\frac{\bar q^b_j}{b_j}\Big)-\theta^b_j. \tag{EC.104}$$
--   Then
--
--   1. $(0,\mu)\in\Gamma\times\mathcal U$;
--   2. $(\theta^s,\bar x,\bar q^s,\bar q^b)$ is a competitive equilibrium under $(0,\mu)$;
--   3. its platform revenue equals the optimal value of (7):
--   $$\sum_{(i,j)\in E}(\mu^s_i+\mu^b_j)\bar x_{ij}=h(\bar q^s,\bar q^b)=\tilde V_{opt}.$$
--
--   Combined with the bound (6), this shows that the relaxation (7) is tight: $V_{opt}=\tilde V_{opt}$, attained by a subscription-only fee profile.
-- source:
--   Birge, Candogan, Chen, Saban, Optimal Commissions and Subscriptions in Networked Markets, SSRN abstract 3259716 (version of 2019-09-13), EC.3.1, proof of Theorem 1, Step (i-2), (EC.103)–(EC.110), pp. ec40–ec42 (PDF 84–86)

import Mathlib
import Definitions.Def_NetworkedMarkets_Relaxation_Setting

open Filter Topology

namespace NetworkedMarkets.Relaxation

theorem step_i_2_subscription_implementation {S B : Type*} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
    (M : Market S B)
    (hM : M.Standing)
    (x : S → B → ℝ) (qs : S → ℝ) (qb : B → ℝ) (hopt : M.IsOpt7 x qs qb)
    (θb : B → ℝ) (θs : S → ℝ) (ηb : B → ℝ) (ηs : S → ℝ) (π : S → B → ℝ)
    (hdual : M.IsSpecialDual x qs qb θb θs ηb ηs π) :
    (M.subscriptionFees qs qb θb θs).InGammaU ∧
      M.IsCE (M.subscriptionFees qs qb θb θs) θs x qs qb ∧
      M.rev (M.subscriptionFees qs qb θb θs) θs x = M.h qs qb := by sorry

end NetworkedMarkets.Relaxation
