-- Prove2me | Theorems.Thm_MinimaxSLP_RhsExtremal_Zhat_le_ZhatDD
-- name    : MinimaxSLP.RhsExtremal.Zhat_le_ZhatDD
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T02:16:53.213987+00:00
-- url     : https://prove2.me/theorems/9f504fbd-105f-471c-bd82-f2fcfb2bd504
-- title:
--   Proof of Theorem 3.3, p. 590 — every P ∈ 𝒫 gives a feasible point of (16) of equal value, so Ẑ(x) ≤ Ẑ_DD(x)
-- statement:
--   Under Assumptions 2, 3 (at the constant $q$) and 5, and $\alpha_k\ge 0$, fix $x\in\mathbb R^n$. For every distribution $P\in\mathcal P$ (mean $\mu$, second-moment matrix $Q$):
--
--   1. $h\mapsto\mathbb U(\mathcal Q(h,x))$ is $P$-integrable;
--   2. there is a feasible point $(V_k^i,v_k^i,v_{k0}^i)_{k,i}$ of (16) whose objective value equals $\mathbb E_P[\mathbb U(\mathcal Q(\tilde h,x))]$.
--
--   Moreover the objective of (16) is bounded above on its feasible set, and
--   $$
--   \hat Z(x)=\sup_{P\in\mathcal P}\mathbb E_P\big[\mathbb U(\mathcal Q(\tilde h,x))\big]\le \hat Z_{DD}(x).
--   $$
--
--   In the paper the feasible point is formed from the probabilities $v_{k0}^i$ of the events "$(k,i)$ attains $\max_{l,j}(\alpha_l(\tilde h-Tx)'p_j+\beta_l)$" and the corresponding conditional first and second moments of $\tilde h$. This is the upper half of the sandwich that proves Theorem 3.3.
--
--   **Formalization Note** The printed $\hat Z(x)$ and $\hat Z_{DD}(x)$ are real `sSup`s; the stronger per-distribution statement (items 1–2) and the bound on (16) make the inequality independent of junk values. Ties in the argmax are the prover's to break.
-- source:
--   Bertsimas, Doan, Natarajan & Teo, Models for Minimax Stochastic Linear Optimization Problems with Risk Aversion, Math. Oper. Res. 35(3), 2010, p. 590, proof of Theorem 3.3

import Mathlib
import Definitions.Def_MomentDRO_Conf_Setting
import Definitions.Def_MinimaxSLP_RhsExtremal_Model

namespace MinimaxSLP.RhsExtremal

open MeasureTheory Matrix

/-- Proof of Theorem 3.3, p. 590: every `P ∈ 𝒫` makes `𝕌(𝒬(·, x))` integrable and yields a
feasible point of (16) whose objective value equals `E_P[𝕌(𝒬(h̃, x))]` (the conditional moments
of `h̃` on the cells where the pair `(k, i)` attains the maximum); the objective of (16) is
bounded above on its feasible set; hence `Ẑ(x) = sup_{P ∈ 𝒫} E_P[𝕌(𝒬(h̃, x))] ≤ Ẑ_DD(x)`. -/
theorem Zhat_le_ZhatDD {r d n K N : ℕ} [NeZero K]
    (W : Matrix (Fin r) (Fin d) ℝ) (T : Matrix (Fin r) (Fin n) ℝ) (q : Fin d → ℝ)
    (α β : Fin K → ℝ) (ps : Fin N → Fin r → ℝ) (μ : Fin r → ℝ) (Q : Matrix (Fin r) (Fin r) ℝ)
    (hα : ∀ k, 0 ≤ α k)
    (hA2 : ∀ z : Fin r → ℝ, ∃ w : Fin d → ℝ, 0 ≤ w ∧ W *ᵥ w = z)
    (hA3 : ∃ π : Fin r → ℝ, Wᵀ *ᵥ π ≤ q)
    (hA5 : Set.range ps = Set.extremePoints ℝ {π : Fin r → ℝ | Wᵀ *ᵥ π ≤ q})
    (x : Fin n → ℝ) :
    (∀ P ∈ MinimaxSLP.ObjSDP.momentClass μ Q,
      Integrable (fun h => MinimaxSLP.ObjSDP.disutility α β (MinimaxSLP.RhsSDP.Qval W T q h x)) P ∧
      ∃ s ∈ feasible16 K N μ Q,
        obj16 T α β ps x s = ∫ h, MinimaxSLP.ObjSDP.disutility α β (MinimaxSLP.RhsSDP.Qval W T q h x) ∂P) ∧
    BddAbove (obj16 T α β ps x '' feasible16 K N μ Q) ∧
    MinimaxSLP.RhsSDP.Zhat W T q α β μ Q x ≤ ZhatDD T α β ps μ Q x := by sorry

end MinimaxSLP.RhsExtremal
