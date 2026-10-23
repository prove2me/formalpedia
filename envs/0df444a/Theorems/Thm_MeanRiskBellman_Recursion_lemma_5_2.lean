-- Prove2me | Theorems.Thm_MeanRiskBellman_Recursion_lemma_5_2
-- name    : MeanRiskBellman.Recursion.lemma_5_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T07:20:38.286996+00:00
-- url     : https://prove2.me/theorems/be16fa47-8976-481b-a8a7-d5b33881cefe
-- title:
--   Lemma 5.2, p. 13 — the upper image of the one-time-step problem D̃_t(v_t) equals P_t(v_t)
-- statement:
--   In the mean-risk market under Assumption 2.2, for every $t=0,\dots,T-1$ and every $\mathcal F_t$-measurable $v_t$, the upper image of the one-time-step problem
--   $$\tilde D_t(v_t):\quad\min_{\psi_t,x}\ \Gamma_t(-x)\ \text{ w.r.t. }\le_{L_t(\mathbb R^2_+)}\quad\text{s.t. } S_t^\top\psi_t=v_t,\ \psi_t\in\Phi_t,\ x\in\mathcal P_{t+1}(S_{t+1}^\top\psi_t),$$
--   namely $\tilde{\mathcal P}_t(v_t)=\operatorname{cl}\big(\{\Gamma_t(-x)\mid(\psi_t,x)\text{ feasible for }\tilde D_t(v_t)\}+L_t(\mathbb R^2_+)\big)$, coincides with the upper image of the original mean-risk problem:
--   $$\tilde{\mathcal P}_t(v_t)=\mathcal P_t(v_t).\tag{5.3}$$
--   Here $\mathcal P_T(v_T)=\{(-v_T,-v_T)\}+L_T(\mathbb R^2_+)$ by (5.2).
--
--   Together with the removal of the cone, this gives the set-valued Bellman equation of Theorem 5.1.
-- source:
--   Kováčová & Rudloff, Time consistency of the mean-risk problem, arXiv:1806.10981v2, p. 13, Lemma 5.2, eq. (5.3) (proof pp. 30–31)

import Mathlib
import Definitions.Def_MeanRiskBellman_Recursion_Model

open MeasureTheory Filter Topology
open scoped Pointwise

namespace MeanRiskBellman.Recursion

theorem lemma_5_2 {Ω : Type*} [Fintype Ω] [MeasurableSpace Ω] (M : Market Ω)
    (hM : M.Assumptions) (t : ℕ) (ht : t < M.T) (v : Ω → ℝ)
    (hv : StronglyMeasurable[M.ℱ t] v) :
    upperImageTilde M t v = upperImage M t v := by sorry

end MeanRiskBellman.Recursion
