-- Prove2me | Theorems.Thm_NonstatRL_Oracle_lemma2_dual_span
-- name    : NonstatRL.Oracle.lemma2_dual_span
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-10-22T18:11:40.899044+00:00
-- url     : https://prove2.me/theorems/fb5b4adb-52df-47c2-8c56-f67ed2298aed
-- title:
--   Lemma 2, p. 33 — dual solutions have span at most $2D$
-- statement:
--   Let $(\mathcal S,\mathcal A,p)$ be a finite MDP with rewards $r(s,a)\in[0,1]$, allowed action sets $\mathcal A_s$, and diameter $D$ (Definition 1: for every ordered pair of states $s,s'$ some deterministic stationary policy using allowed actions reaches $s'$ from $s$ in expected time at most $D$; return times included). Let $(\rho,\gamma)$ be a feasible solution of the dual LP $D(r,p)$ in (16), i.e.
--   $$\rho+\gamma(s)\ge r(s,a)+\sum_{s'}p(s'|s,a)\gamma(s')\quad\text{for all } s\text{ and } a\in\mathcal A_s,$$
--   with $\rho\le1$. Then
--   $$\max_{s,s'\in\mathcal S}\{\gamma(s)-\gamma(s')\}\le 2D.$$
--
--   **Formalization note.** The printed Lemma 2 assumes only feasibility. Without a bound on $\rho$ it fails: any $\gamma$ is feasible together with $\rho=1+\max\gamma-\min\gamma$, so the span is unbounded. Jaksch et al. state the bound for the optimal solution. We add the hypothesis $\rho\le1$, which holds at $\rho=\rho^*$ because rewards lie in $[0,1]$; that is the only case used in the proof of Proposition 1. The diameter hypothesis is the extended-real bound $\mathrm{diam}\le D$.
-- source:
--   Cheung, Simchi-Levi & Zhu, Non-Stationary Reinforcement Learning: The Blessing of (More) Optimism, arXiv:1906.02922v4, Appendix A.1, p. 33, Lemma 2 (extracted from Jaksch, Ortner & Auer 2010, Section 4.3.1)

import Mathlib
import Definitions.Def_FiniteMDPLearning
import Definitions.Def_NonstatRL_Oracle_Model

open BanditAlgorithm ENNReal MeasureTheory

namespace NonstatRL.Oracle

/-- Lemma 2, Appendix A.1, p. 33 (Jaksch et al. 2010, §4.3.1), for dual-feasible
solutions with ρ ≤ 1. -/
theorem lemma2_dual_span {S A : ℕ} (M : FiniteMDP S A)
    (As : Fin S → Finset (Fin A)) (D : ℝ)
    (hD : diameter M As ≤ ENNReal.ofReal D) (ρ : ℝ) (γ : Fin S → ℝ)
    (hfeas : DualFeasible M.r (fun s a s' => (M.P s a s' : ℝ)) As ρ γ)
    (hρ : ρ ≤ 1) :
    ∀ s s' : Fin S, γ s - γ s' ≤ 2 * D := by sorry

end NonstatRL.Oracle
