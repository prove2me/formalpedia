-- Prove2me | Theorems.Thm_MinimaxSLP_ObjExtremal_jensen_step
-- name    : MinimaxSLP.ObjExtremal.jensen_step
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T01:14:53.051389+00:00
-- url     : https://prove2.me/theorems/e5492c7f-8c50-4f71-95b9-070da2753782
-- title:
--   Proof of Theorem 2.2, p. 586 — Jensen: $\mathbb E_P[\mathcal Q(\tilde r,x)]\le\mathcal Q(\mathbb E_P[\tilde r],x)$, and the expectation is finite
-- statement:
--   Let $x$ be such that $X(x)\neq\emptyset$, and assume Assumption 3. Let $P$ be a probability distribution of a random vector $\tilde r$ on $\mathbb R^d$ whose coordinates are integrable. Then $\mathcal Q(\tilde r,x)$ is integrable under $P$, in particular $\mathbb E_P[\mathcal Q(\tilde r,x)]>-\infty$, and
--   $$
--   \mathbb E_P\big[\mathcal Q(\tilde r,x)\big]\ \le\ \mathcal Q\big(\mathbb E_P[\tilde r],x\big).
--   $$
--   Moreover $\mathcal Q(0,x)=0$, so the right-hand side vanishes when $\mathbb E_P[\tilde r]=0$.
--
--   In the proof of Theorem 2.2 this is applied to the centred normal vectors $\tilde r_k$, and shows that the $\sqrt\epsilon$ correction term is bounded below and vanishes as $\epsilon\downarrow0$.
--
--   **Formalization Note** The paper applies the inequality to $\tilde r_k\sim\mathbb N\big(0,(V_kv_{k0}-v_kv_k')/v_{k0}^2\big)$; the statement here is the general form for any probability measure with integrable coordinates. The paper attributes finiteness to "Assumptions 1–4"; only $X(x)\neq\emptyset$ and Assumption 3 are needed.
-- source:
--   Bertsimas, Doan, Natarajan & Teo, Models for Minimax Stochastic Linear Optimization Problems with Risk Aversion, Math. Oper. Res. 35(3), 2010, p. 586, proof of Theorem 2.2

import Mathlib
import Definitions.Def_MomentDRO_Conf_Setting
import Definitions.Def_MinimaxSLP_ObjExtremal_Model

open MeasureTheory Matrix Filter Topology

namespace MinimaxSLP.ObjExtremal

/-- Proof of Theorem 2.2 (p. 586), Jensen step, in general form: for every probability measure
`P` on `ℝ^d` with integrable coordinates, `𝒬(·, x)` is `P`-integrable (so its expectation is
`> −∞`) and `E_P[𝒬(r̃, x)] ≤ 𝒬(E_P[r̃], x)`; moreover `𝒬(0, x) = 0`, the value at mean `0`. -/
theorem jensen_step {n r d : ℕ}
    (W : Matrix (Fin r) (Fin d) ℝ) (T : Matrix (Fin r) (Fin n) ℝ) (h : Fin r → ℝ)
    (hA3 : ∀ q : Fin d → ℝ, ∃ π : Fin r → ℝ, Wᵀ *ᵥ π ≤ q)
    (x : Fin n → ℝ) (hrec : (MinimaxSLP.ObjSDP.recourseSet W T h x).Nonempty)
    (P : Measure (Fin d → ℝ)) [IsProbabilityMeasure P]
    (hint : ∀ i : Fin d, Integrable (fun ρ : Fin d → ℝ => ρ i) P) :
    Integrable (fun ρ => MinimaxSLP.ObjSDP.Qval W T h ρ x) P ∧
    ∫ ρ, MinimaxSLP.ObjSDP.Qval W T h ρ x ∂P ≤ MinimaxSLP.ObjSDP.Qval W T h (fun i => ∫ ρ, ρ i ∂P) x ∧
    MinimaxSLP.ObjSDP.Qval W T h 0 x = 0 := by sorry

end MinimaxSLP.ObjExtremal
