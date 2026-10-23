-- Prove2me | Theorems.Thm_NonstatRL_PerStep_lemma2_span_le_two_diameter
-- name    : NonstatRL.PerStep.lemma2_span_le_two_diameter
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-16T06:16:48.217251+00:00
-- url     : https://prove2.me/theorems/95c4d9a6-0b90-417c-b469-cc5b376eb420
-- title:
--   Lemma 2 — dual bias span bounded by twice the diameter
-- statement:
--   Let $r$ be nonnegative on a finite MDP with a nonempty allowed action set at every state, and let the transition model have diameter at most $D$. Suppose $(\rho,\gamma)$ is feasible for the occupancy-program dual and $\rho\le2$. Then
--
--   $$
--   \gamma(s)-\gamma(s')\le 2D\qquad\text{for every pair of states }s,s'.
--   $$
--
--   This is the bias-span estimate used in the optimism analysis. **Formalization Note** The printed Lemma 2 omits $\rho\le2$ and is false for arbitrary feasible dual variables; the bound is supplied explicitly. The diameter counts return times when $s=s'$.
-- source:
--   Cheung, Simchi-Levi & Zhu, Non-Stationary Reinforcement Learning: The Blessing of (More) Optimism, arXiv:1906.02922v4, p. 33, Lemma 2 (pinned gain bound)

import Mathlib
import Definitions.Def_NonstatRL_Oracle_Model

open BanditAlgorithm ENNReal

namespace NonstatRL.PerStep

theorem lemma2_span_le_two_diameter {S A : ℕ} (hS : 0 < S)
    (r : Fin S → Fin A → ℝ) (As : Fin S → Finset (Fin A))
    (hAs : ∀ s, (As s).Nonempty)
    (hr : ∀ s a, a ∈ As s → 0 ≤ r s a)
    (Mw : FiniteMDP S A) (D ρ : ℝ) (γ : Fin S → ℝ)
    (hdiam : NonstatRL.Oracle.diameter Mw As ≤ ENNReal.ofReal D)
    (hdual : NonstatRL.Oracle.DualFeasible r (fun s a s' => (Mw.P s a s' : ℝ)) As ρ γ)
    (hρ : ρ ≤ 2) :
    ∀ s s' : Fin S, γ s - γ s' ≤ 2 * D := by sorry

end NonstatRL.PerStep
