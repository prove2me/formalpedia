-- Prove2me | Theorems.Thm_NonstatRL_Oracle_eq18_optGain_drift
-- name    : NonstatRL.Oracle.eq18_optGain_drift
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-16T04:28:31.270417+00:00
-- url     : https://prove2.me/theorems/1312fc60-ddc5-4cc4-89ef-8359ab85a3cb
-- title:
--   (18), p. 33 — drift bound for optimal gains
-- statement:
--   Consider two rounds $t\le\tau$ of a nonstationary finite MDP. Let $\rho_t^*$ and $\rho_\tau^*$ be the optimal occupancy-LP gains, $B_{r,q}$ the largest one-step reward drift, $B_{p,q}$ the largest one-step transition drift, and $D_{\max}$ a common diameter bound. Then
--
--   $$\rho_\tau^*\ge\rho_t^*-\sum_{q=t}^{\tau-1}(B_{r,q}+2D_{\max}B_{p,q}).$$
--
--   The inequality controls how far the stationary optimal gain can change inside a window. The rewards and transitions are probability models on allowed state–action pairs.
--
--   **Formalization Note** States and each state's allowed-action set are nonempty. Paper round $t$ is Lean index $t-1$, so the sum is over a half-open integer range. Diameter uses extended nonnegative reals and includes same-state returns.
-- source:
--   Cheung, Simchi-Levi & Zhu, Non-Stationary Reinforcement Learning: The Blessing of (More) Optimism, arXiv:1906.02922v4, p. 33, Appendix A.2, (18)

import Mathlib
import Definitions.Def_FiniteMDPLearning
import Definitions.Def_NonstatRL_Oracle_Model

open BanditAlgorithm ENNReal

namespace NonstatRL.Oracle

/-- Equation (18), Appendix A.2, p. 33. -/
theorem eq18_optGain_drift {S A : ℕ} (M : ℕ → FiniteMDP S A)
    (As : Fin S → Finset (Fin A)) (hS : 0 < S)
    (hAs : ∀ s, (As s).Nonempty) (T : ℕ) (Dmax : ℝ)
    (hD : ∀ u, u < T → diameter (M u) As ≤ ENNReal.ofReal Dmax)
    (t τ : ℕ) (htτ : t ≤ τ) (hτ : τ < T) :
    optGain (M t) As -
      (∑ q ∈ Finset.Ico t τ,
        (rewardDrift M As q + 2 * Dmax * transDrift M As q)) ≤
      optGain (M τ) As := by sorry

end NonstatRL.Oracle
