-- Prove2me | Theorems.Thm_MajorityAttack_NegCost_lemma_1
-- name    : MajorityAttack.NegCost.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:41:11.464113+00:00
-- url     : https://prove2.me/theorems/44435a67-c8cb-4077-95b0-7f3771b35214
-- title:
--   Lemma 1 — a sub-majority threshold for negative attack cost
-- statement:
--   Let $H,\tau,\mathcal L>0$ and suppose the attack-chain reward per block strictly exceeds the incumbent reward, $\widetilde\rho>\rho$. For a nondecreasing convex mining cost on nonnegative hash powers and an attained attack-chain profit maximizer $\widetilde h_A$, there exists a threshold $\widehat h$ with $0<\widehat h<H/2$ such that every incumbent power $h^*\ge\widehat h$ has strictly negative net attack cost:
--
--   $$\exists\,\widehat h\in(0,H/2)\quad\forall h^*\ge\widehat h,\quad C_{\rm net}(h^*,\widetilde h_A)<0.$$
--
--   The threshold applies to a continuum of possible incumbent powers. It is the economic cost result combined with the fee comparison in Proposition 1.
--
--   **Formalization Note** Convexity on $[0,\infty)$ and attainment of $\widetilde h_A$ are explicit additions needed for the attack-profit model. The incumbent power is a free nonnegative value, which strengthens the paper's version where $h^*$ is a pre-attack optimum.
-- source:
--   Gans & Halaburda, “Zero Cost” Majority Attacks on Permissionless Blockchains, arXiv:2308.06568v1, p. 11, Lemma 1

import Mathlib
import Definitions.Def_MajorityAttack_NegCost_Model

namespace MajorityAttack.NegCost

/-- Lemma 1, p. 11: a uniform sub-majority incumbent threshold for negative attack cost. -/
theorem lemma_1 (τ H L ρ ρt : ℝ) (c : ℝ → ℝ) (htil : ℝ)
    (hτ : 0 < τ) (hH : 0 < H) (hL : 0 < L) (hreward : ρ < ρt)
    (hc : CostStanding c) (hopt : IsAttackOptimum (τ * H) ρt c htil) :
    ∃ hhat : ℝ, 0 < hhat ∧ hhat < H / 2 ∧
      ∀ hstar : ℝ, hhat ≤ hstar → netCost τ H L ρ ρt c htil hstar < 0 := by sorry

end MajorityAttack.NegCost
