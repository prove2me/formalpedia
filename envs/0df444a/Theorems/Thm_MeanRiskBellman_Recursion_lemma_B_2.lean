-- Prove2me | Theorems.Thm_MeanRiskBellman_Recursion_lemma_B_2
-- name    : MeanRiskBellman.Recursion.lemma_B_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T07:20:22.252933+00:00
-- url     : https://prove2.me/theorems/62ecabe8-9a9e-49f8-88ba-46d86956e9d7
-- title:
--   Lemma B.2, p. 30 — D_t(v_t) and the auxiliary problem D̄_t(v_t) have the same image: Γ_t(Ψ_t(v_t)) = Γ_t(Ψ̄_t(v_t))
-- statement:
--   In the mean-risk market under Assumption 2.2, for every time $t=0,\dots,T-1$ and every $\mathcal F_t$-measurable investment $v_t$, the mean-risk problem $D_t(v_t)$ and the auxiliary problem $\bar D_t(v_t)$ share the same image of the feasible set:
--   $$\Gamma_t(\Psi_t(v_t))=\Gamma_t(\bar\Psi_t(v_t)),$$
--   that is,
--   $$\{\Gamma_t(V_T(\psi))\mid\psi\in\Psi_t(v_t)\}=\{\Gamma_t(-x)\mid S_t^\top\psi_t=v_t,\ \psi_t\in\Phi_t,\ x\in\Gamma_{t+1}(\Psi_{t+1}(S_{t+1}^\top\psi_t))\},$$
--   where for $t=T-1$ the inner set is $\Gamma_T(\Psi_T(v_T))=\{(-v_T,-v_T)\}$ by convention (B.2).
--
--   The auxiliary problem is the stepping stone from the multi-period problem to the one-time-step problem $\tilde D_t(v_t)$ of Lemma 5.2.
-- source:
--   Kováčová & Rudloff, Time consistency of the mean-risk problem, arXiv:1806.10981v2, p. 30, Lemma B.2 (with problem D̄_t(v_t), p. 29, and (B.2), p. 30)

import Mathlib
import Definitions.Def_MeanRiskBellman_Recursion_Model

open MeasureTheory Filter Topology
open scoped Pointwise

namespace MeanRiskBellman.Recursion

theorem lemma_B_2 {Ω : Type*} [Fintype Ω] [MeasurableSpace Ω] (M : Market Ω)
    (hM : M.Assumptions) (t : ℕ) (ht : t < M.T) (v : Ω → ℝ)
    (hv : StronglyMeasurable[M.ℱ t] v) :
    image M t v = imageBar M t v := by sorry

end MeanRiskBellman.Recursion
