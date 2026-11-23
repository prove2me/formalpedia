-- Prove2me | Theorems.Thm_MeanRiskBellman_Recursion_Supplement_theorem_3_2
-- name    : MeanRiskBellman.Recursion.Supplement.theorem_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T12:15:07.163937+00:00
-- url     : https://prove2.me/theorems/950e2cf1-f9b0-4dcf-bcb4-42cf4c39488e
-- title:
--   Theorem 3.2, p. 10 — the family of mean-risk problems is time consistent w.r.t. weak minimizers
-- statement:
--   Work in the market model of the mission under Assumption 2.2: a finite filtered probability space $(\Omega,\mathcal F,(\mathcal F_t)_{t=0}^T,P)$ with $\mathcal F_0$ trivial, $\mathcal F_T=\mathcal F$ and $P(A)>0$ for every nonempty event $A$; adapted discounted prices $S_t\in\mathbb R^d$; closed, conditionally convex trading constraints $\Phi_t\subseteq L_t(\mathbb R^d)$; and a time consistent dynamic convex risk measure $(\rho_t)_{t=0}^T$. For an $\mathcal F_t$-measurable wealth $v_t$, the mean-risk problem $D_t(v_t)$ minimizes $\Gamma_t(V_T(\psi))=\bigl(-\mathbb E_t(v_T^\psi),\rho_t(v_T^\psi)\bigr)$, $v_T^\psi=S_T^\top\psi_{T-1}$, over the feasible portfolios $\psi\in\Psi_t(v_t)$ with respect to the cone $L_t(\mathbb R^2_+)$; $\psi$ is a weak minimizer if
--   $$\bigl(\Gamma_t(V_T(\psi))-\operatorname{int}L_t(\mathbb R^2_+)\bigr)\cap\Gamma_t(\Psi_t(v_t))=\emptyset .$$
--
--   **Theorem 3.2.** The family $\mathcal D$ of mean-risk problems is time consistent w.r.t. weak minimizers: for every time $t$ with $t+1<T$, every $\mathcal F_t$-measurable wealth $v_t$ and every trading strategy $\psi$,
--   $$(\psi_s)_{s=t,\dots,T-1}\ \text{weak minimizer of } D_t(v_t)\ \Longrightarrow\ (\psi_s)_{s=t+1,\dots,T-1}\ \text{weak minimizer of } D_{t+1}\bigl(S_{t+1}^\top\psi_t\bigr).$$
--
--   An investor who chooses a weakly efficient mean-risk portfolio at time $t$ and re-optimizes at time $t+1$ with the wealth the portfolio has produced finds the remainder of the original plan still weakly efficient, so the plan is carried out as made. The paper notes that time consistency fails in general for (non-weak) minimizers.
--
--   **Formalization Note** The hypotheses are the published standing assumptions of the mission (Assumption 2.2, items 1, 2 and 4); item 3, $\Psi_0(v_0)\neq\emptyset$, is not assumed. All relations are pointwise in $\omega$, which agrees with the paper's almost-sure relations on a finite space with positive atom probabilities. Strategies are indexed by $\mathbb N$, so the truncated strategy is the same $\psi$ read from index $t+1$.
--
--   Differences from the source:
--   - generalization: Assumption 2.2 includes item 3, Ψ_0(v_0) ≠ ∅ → not assumed; reason: the theorem and its proof never use it, and the Lean statement specializes to the source's by adding it.
--   - reading: Definition 3 quantifies over t = 0, …, T−1 → t + 1 < T; reason: at t = T−1 the truncated strategy is empty and D_T is not a problem of the family D (p. 8), so the clause has no content there.
--   - encoding: int L_t(ℝ²_+) and P-a.s. relations in L_t(ℝ²) → F_t-measurable vectors strictly positive in both components at every ω, pointwise relations; reason: on a finite space with positive atom probabilities these are the same sets and relations.
--   - encoding: the truncation (ψ_s)_{s=t+1,…,T−1} → the same ℕ-indexed ψ; reason: D_{t+1} reads only the indices t+1, …, T−1.
-- source:
--   Kováčová & Rudloff, Time consistency of the mean-risk problem, arXiv:1806.10981v2, p. 10, Theorem 3.2 (with Definition 3, p. 10; (2.6), p. 9; Assumption 2.2, p. 6)

import Mathlib
import Definitions.Def_MeanRiskBellman_Recursion_Supplement_WeakMinimizer

open MeasureTheory

namespace MeanRiskBellman.Recursion.Supplement

theorem theorem_3_2 {Ω : Type*} [Fintype Ω] [MeasurableSpace Ω] (M : Market Ω)
    (hM : M.Assumptions) : TimeConsistentWeak M := by sorry

end MeanRiskBellman.Recursion.Supplement
