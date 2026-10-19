-- Prove2me | Theorems.Thm_NetworkedMarkets_Relaxation_corollary_1
-- name    : NetworkedMarkets.Relaxation.corollary_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T17:24:53.361119+00:00
-- url     : https://prove2.me/theorems/afe03fa0-1dd1-4b9a-8c18-de0034d3b7cf
-- title:
--   Corollary 1, p. 11 — all competitive equilibria under the same fees yield the same platform revenue
-- statement:
--   Under the standing assumptions of §2, fix $(\gamma,\mu)\in\Gamma\times\mathcal U$. For any two competitive equilibria $(p,x,q^s,q^b)$ and $(p',x',q'^s,q'^b)$ in $\mathcal X(\gamma,\mu)$, the platform revenue (3a) is the same:
--   $$\sum_{(i,j)\in E}(\gamma^s_i+\gamma^b_j)p_ix_{ij}+\sum_{(i,j)\in E}(\mu^s_i+\mu^b_j)x_{ij}=\sum_{(i,j)\in E}(\gamma^s_i+\gamma^b_j)p'_ix'_{ij}+\sum_{(i,j)\in E}(\mu^s_i+\mu^b_j)x'_{ij}.$$
--
--   Hence the revenue $V(\gamma,\mu)$ of a commission-subscription pair is well defined, and a pair is optimal exactly when this common revenue equals $V_{opt}$.
-- source:
--   Birge, Candogan, Chen, Saban, Optimal Commissions and Subscriptions in Networked Markets, SSRN abstract 3259716 (version of 2019-09-13), p. 11, Corollary 1

import Mathlib
import Definitions.Def_NetworkedMarkets_Relaxation_Setting

open Filter Topology

namespace NetworkedMarkets.Relaxation

theorem corollary_1 {S B : Type*} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
    (M : Market S B) (hM : M.Standing1)
    (f : Fees S B) (hf : f.InGammaU)
    (p : S → ℝ) (x : S → B → ℝ) (qs : S → ℝ) (qb : B → ℝ)
    (p' : S → ℝ) (x' : S → B → ℝ) (qs' : S → ℝ) (qb' : B → ℝ)
    (hce : M.IsCE f p x qs qb) (hce' : M.IsCE f p' x' qs' qb') :
    M.rev f p x = M.rev f p' x' := by sorry

end NetworkedMarkets.Relaxation
