-- Prove2me | Theorems.Thm_MinimaxSLP_RhsExtremal_dual16_optimal_zero_or_positive
-- name    : MinimaxSLP.RhsExtremal.dual16_optimal_zero_or_positive
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T02:18:11.938834+00:00
-- url     : https://prove2.me/theorems/1b8355d6-f8db-46a6-a3f1-2a7a56e92022
-- title:
--   Proof of Theorem 3.3, p. 590 — (16) has an optimal solution whose blocks have v_k0^i > 0 or vanish
-- statement:
--   Let $\mu\in\mathbb R^r$ and a symmetric $Q\in\mathbb R^{r\times r}$ satisfy $Q-\mu\mu'\succ 0$ (Assumption 4), let $N\ge 1$, and fix the data $T,\alpha,\beta,p_1,\dots,p_N,x$ of the objective of (16). Then (16) has an optimal solution $(V_k^i,v_k^i,v_{k0}^i)_{k,i}$, that is, a feasible point at which the objective
--   $$
--   \sum_{k=1}^K\sum_{i=1}^N\big(\alpha_k p_i'v_k^i+v_{k0}^i(\beta_k-\alpha_k p_i'Tx)\big)
--   $$
--   attains its maximum over the feasible set, such that for every pair $(k,i)$ either $v_{k0}^i>0$ or $(V_k^i,v_k^i,v_{k0}^i)=0$.
--
--   The paper writes "without loss of generality, we can again assume that $v_{k0}^i>0$ for all $k$ and $i$ (see Theorem 2.2)"; the blocks with $v_{k0}^i=0$ are discarded from the mixture, which is the form stated here. This optimal solution is the input to the construction of the extremal distribution.
--
--   **Formalization Note** "$v_{k0}^i>0$ for all $k,i$" literally can fail at every optimum, so the zero-or-positive form is used; the zero blocks receive weight $0$ in the mixture. $N\ge 1$ is assumed explicitly (with $N=0$ the program is infeasible); under Assumptions 2, 3 and 5 it holds automatically.
-- source:
--   Bertsimas, Doan, Natarajan & Teo, Models for Minimax Stochastic Linear Optimization Problems with Risk Aversion, Math. Oper. Res. 35(3), 2010, p. 590, proof of Theorem 3.3; zero-weight argument in the proof of Theorem 2.2, p. 587

import Mathlib
import Definitions.Def_MomentDRO_Conf_Setting
import Definitions.Def_MinimaxSLP_RhsExtremal_Model

namespace MinimaxSLP.RhsExtremal

open MeasureTheory Matrix

/-- Proof of Theorem 3.3, p. 590: under Assumption 4 (`Q` symmetric, `Q − μμ′ ≻ 0`) and
`N ≥ 1`, the problem (16) has an optimal solution in which every block either has
`v_k0^i > 0` or is identically zero (the reading of "without loss of generality `v_k0^i > 0`
(see Theorem 2.2)"). -/
theorem dual16_optimal_zero_or_positive {r n K N : ℕ} [NeZero K]
    (T : Matrix (Fin r) (Fin n) ℝ) (α β : Fin K → ℝ) (ps : Fin N → Fin r → ℝ)
    (μ : Fin r → ℝ) (Q : Matrix (Fin r) (Fin r) ℝ)
    (hN : 0 < N)
    (hQ : Q.IsSymm) (hA4 : (Q - Matrix.vecMulVec μ μ).PosDef)
    (x : Fin n → ℝ) :
    ∃ s ∈ feasible16 K N μ Q,
      IsGreatest (obj16 T α β ps x '' feasible16 K N μ Q) (obj16 T α β ps x s) ∧
      ∀ k i, 0 < (s k i).2.2 ∨ s k i = 0 := by sorry

end MinimaxSLP.RhsExtremal
