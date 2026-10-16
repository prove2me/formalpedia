-- Prove2me | Theorems.Thm_NonstatRL_Oracle_eq19_dual_drift
-- name    : NonstatRL.Oracle.eq19_dual_drift
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-16T04:28:36.077169+00:00
-- url     : https://prove2.me/theorems/ebda548d-f690-4fd3-86c4-a8349dc13401
-- title:
--   (19), p. 33 — pathwise dual drift inequality
-- statement:
--   Fix rounds $t\le\tau$, an allowed state–action pair $(s,a)$, and a dual potential $\gamma_t^*$ that is feasible at the optimal gain $\rho_t^*$ and lies between $0$ and $2D_{\max}$ at every state. Then
--
--   $$\rho_t^*\ge r_\tau(s,a)+\left[\sum_{s'}p_\tau(s'\mid s,a)\gamma_t^*(s')-\gamma_t^*(s)\right]-\sum_{q=t}^{\tau-1}(B_{r,q}+2D_{\max}B_{p,q}).$$
--
--   The inequality applies at each possible allowed pair, and therefore along a realized trajectory. It is the second drift estimate used before the window calculation.
--
--   **Formalization Note** The paper writes the pair realized at round $\tau$; the displayed inequality is pointwise in the pair. The potential is quantified through exactly its dual-feasibility and boundedness properties. Indices in Lean are zero based; the state set and every allowed-action set are nonempty.
-- source:
--   Cheung, Simchi-Levi & Zhu, Non-Stationary Reinforcement Learning: The Blessing of (More) Optimism, arXiv:1906.02922v4, p. 33, Appendix A.2, (19)

import Mathlib
import Definitions.Def_FiniteMDPLearning
import Definitions.Def_NonstatRL_Oracle_Model

open BanditAlgorithm ENNReal

namespace NonstatRL.Oracle

/-- Equation (19), Appendix A.2, p. 33, for each allowed pair. -/
theorem eq19_dual_drift {S A : ℕ} (M : ℕ → FiniteMDP S A)
    (As : Fin S → Finset (Fin A)) (hS : 0 < S)
    (hAs : ∀ s, (As s).Nonempty) (T : ℕ) (Dmax : ℝ)
    (hD : ∀ u, u < T → diameter (M u) As ≤ ENNReal.ofReal Dmax)
    (t τ : ℕ) (htτ : t ≤ τ) (hτ : τ < T)
    (γ : Fin S → ℝ)
    (hγ : DualFeasible (M t).r (fun s a s' => ((M t).P s a s' : ℝ))
      As (optGain (M t) As) γ)
    (hγbounds : ∀ s, 0 ≤ γ s ∧ γ s ≤ 2 * Dmax)
    (s : Fin S) (a : Fin A) (ha : a ∈ As s) :
    (M τ).r s a +
      ((∑ s' : Fin S, ((M τ).P s a s' : ℝ) * γ s') - γ s) -
      (∑ q ∈ Finset.Ico t τ,
        (rewardDrift M As q + 2 * Dmax * transDrift M As q)) ≤
      optGain (M t) As := by sorry

end NonstatRL.Oracle
