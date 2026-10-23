-- Prove2me | Theorems.Thm_MeanRiskBellman_Recursion_lemma_3_1
-- name    : MeanRiskBellman.Recursion.lemma_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T07:20:24.941249+00:00
-- url     : https://prove2.me/theorems/1fc6a6fb-c642-44f6-b4ee-bdf4b03adfab
-- title:
--   Lemma 3.1, p. 10 — ψ ∈ Ψ_t(v_t) iff S_t^⊤ψ_t = v_t, ψ_t ∈ Φ_t and (ψ_s)_{s≥t+1} ∈ Ψ_{t+1}(S_{t+1}^⊤ψ_t)
-- statement:
--   In the mean-risk market under Assumption 2.2, let $t$ be a time with $t+1\le T-1$ and $v_t\in L_t$. A trading strategy is feasible, $(\psi_s)_{s=t,\dots,T-1}\in\Psi_t(v_t)$, if and only if
--   $$S_t^\top\psi_t=v_t,\qquad \psi_t\in\Phi_t,\qquad (\psi_s)_{s=t+1,\dots,T-1}\in\Psi_{t+1}\big(S_{t+1}^\top\psi_t\big).$$
--
--   This is the recursive structure of the feasible sets used for Theorem 3.2 and Lemma B.2.
--
--   **Formalization Note.** $\Psi_{t+1}$ is defined for $t+1\le T-1$, hence the hypothesis $t+1<T$. Strategies are sequences indexed by $\mathbb N$ in which only the indices $t,\dots,T-1$ are constrained; the same sequence is tested for membership in $\Psi_t$ and in $\Psi_{t+1}$ (which ignores $\psi_t$).
-- source:
--   Kováčová & Rudloff, Time consistency of the mean-risk problem, arXiv:1806.10981v2, p. 10, Lemma 3.1 (proof p. 33)

import Mathlib
import Definitions.Def_MeanRiskBellman_Recursion_Model

open MeasureTheory Filter Topology
open scoped Pointwise

namespace MeanRiskBellman.Recursion

theorem lemma_3_1 {Ω : Type*} [Fintype Ω] [MeasurableSpace Ω] (M : Market Ω)
    (hM : M.Assumptions) (t : ℕ) (ht : t + 1 < M.T) (v : Ω → ℝ)
    (hv : StronglyMeasurable[M.ℱ t] v) (ψ : ℕ → Ω → Fin M.d → ℝ) :
    ψ ∈ feasible M t v ↔
      value M t (ψ t) = v ∧ ψ t ∈ M.Φ t ∧ ψ ∈ feasible M (t + 1) (value M (t + 1) (ψ t)) := by sorry

end MeanRiskBellman.Recursion
