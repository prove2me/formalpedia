-- Prove2me | Theorems.Thm_NonstatRL_Oracle_eq23_window_bound
-- name    : NonstatRL.Oracle.eq23_window_bound
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-16T04:29:13.480823+00:00
-- url     : https://prove2.me/theorems/ffc054c1-18c6-46ba-bbd7-166cecb34d2d
-- title:
--   (23), p. 34 — one-window bound; (21)–(22) omitted
-- statement:
--   Consider a positive-length window of $W$ rounds beginning at $t$ and contained in a horizon of $T$ rounds. For every allowed history-dependent randomized policy, with a fixed initial state, the sum of stationary optimal gains over the window satisfies
--
--   $$\sum_{\tau=t}^{t+W-1}\rho_\tau^*\ge\mathbb E\!\left[\sum_{\tau=t}^{t+W-1}r_\tau(s_\tau,a_\tau)\right]-2D_{\max}-2W\sum_{q=t}^{t+W-1}(B_{r,q}+2D_{\max}B_{p,q}).$$
--
--   This is the window estimate used when the horizon is partitioned for (24).
--
--   **Formalization Note** Round indices are zero based. At the last window, the printed drift sum includes a term $B_{\cdot,T}$ outside the paper's definition (1). The Lean sum omits that term, treating it as zero; every defined term is retained. The trajectory measure is a probability measure driven by $p_\tau$, and the integrand uses mean rewards. States and allowed-action sets are nonempty.
-- source:
--   Cheung, Simchi-Levi & Zhu, Non-Stationary Reinforcement Learning: The Blessing of (More) Optimism, arXiv:1906.02922v4, p. 34, Appendix A.2, (23)

import Mathlib
import Definitions.Def_FiniteMDPLearning
import Definitions.Def_NonstatRL_Oracle_Model
import Definitions.Def_NonstatRL_Oracle_Trajectory

open BanditAlgorithm ENNReal MeasureTheory

namespace NonstatRL.Oracle

/-- Equation (23), Appendix A.2, p. 34, on a window within the horizon. -/
theorem eq23_window_bound {S A : ℕ} (M : ℕ → FiniteMDP S A)
    (As : Fin S → Finset (Fin A)) (hS : 0 < S)
    (hAs : ∀ s, (As s).Nonempty) (T : ℕ) (Dmax : ℝ)
    (hD : ∀ u, u < T → diameter (M u) As ≤ ENNReal.ofReal Dmax)
    (s₁ : Fin S) (π : MDPPolicy S A) (hπ : IsAllowedPolicy As π)
    (t W : ℕ) (hW : 0 < W) (hEnd : t + W ≤ T) :
    (∫ h, ∑ τ ∈ (Finset.univ.filter fun τ : Fin T =>
        t ≤ (τ : ℕ) ∧ (τ : ℕ) < t + W),
        (M τ).r (h τ).1 (h τ).2 ∂(nsMeasure M s₁ π T)) -
      2 * Dmax - 2 * (W : ℝ) *
        (∑ q ∈ Finset.Ico t (min (t + W) (T - 1)),
          (rewardDrift M As q + 2 * Dmax * transDrift M As q)) ≤
      ∑ τ ∈ Finset.Ico t (t + W), optGain (M τ) As := by sorry

end NonstatRL.Oracle
