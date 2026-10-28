-- Prove2me | Theorems.Thm_NetInspect_Rate_lemma_EC_4
-- name    : NetInspect.Rate.lemma_EC_4
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-21T05:03:17.049489+00:00
-- url     : https://prove2.me/theorems/226ddcd6-e7a7-4ce3-8808-86ac78d2e12b
-- title:
--   Lemma EC.4, p. ec10 — for b2 < m*, any ρ ∈ [0,1]^E summing to b2 is the attack-probability vector of some σ2 ∈ Δ(A2)
-- statement:
--   Let $\mathcal G$ be a detection model and $b_2<m^*$. Let $\rho\in[0,1]^{\mathcal E}$ satisfy $\sum_{e\in\mathcal E}\rho_e=b_2$. Then there is an attack strategy $\sigma^2\in\Delta(\mathcal A_2)$ with
--   $$
--   \rho_{\sigma^2}(e)=\sum_{T\ni e}\sigma^2_T=\rho_e\qquad\text{for all } e\in\mathcal E.
--   $$
--
--   Every feasible vector of attack probabilities is realized by a mixed strategy over attack plans of size at most $b_2$. This is the step of the proof of Theorem 2 that scales an attack strategy of $\Gamma(b_1,1)$ up to one of $\Gamma(b_1,b_2)$.
-- source:
--   Dahan, Sela & Amin, Network Inspection for Detecting Strategic Attacks, arXiv:1705.00349v4, p. ec10, Lemma EC.4

import Mathlib
import Definitions.Def_BlottoLP_Flow_ZeroSum
import Definitions.Def_NetInspect_Rate_Model

namespace NetInspect.Rate

open Finset DetectionModel

/-- Lemma EC.4 (p. ec10): if `b2 < m*` and `ρ ∈ [0,1]^E` sums to `b2`, some attack strategy
`σ2 ∈ Δ(A2)` has attack probabilities `ρ_{σ2}(e) = ρ_e` for every component `e`. -/
theorem lemma_EC_4 {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : DetectionModel V E)
    {b2 : ℕ} (hb2 : b2 < G.mStar) (ρ : E → ℝ) (hρ : ∀ e : E, 0 ≤ ρ e ∧ ρ e ≤ 1)
    (hsum : ∑ e : E, ρ e = (b2 : ℝ)) :
    ∃ σ2 : Act E b2 → ℝ, BlottoLP.Flow.IsMixed σ2 ∧ ∀ e : E, marg σ2 e = ρ e := by sorry

end NetInspect.Rate
