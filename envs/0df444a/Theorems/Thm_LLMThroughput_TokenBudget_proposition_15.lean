-- Prove2me | Theorems.Thm_LLMThroughput_TokenBudget_proposition_15
-- name    : LLMThroughput.TokenBudget.proposition_15
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-24T04:40:51.765211+00:00
-- url     : https://prove2.me/theorems/69e56962-82d8-4c53-b09c-1ca8b52a6bb3
-- title:
--   Proposition 15, p. 40 (corrected: fluid levels Z_f ≥ 0) — the work-conserving LLM fluid model is stable under λ(m_p + m_d) < b_max/t_{b_max}
-- statement:
--   **Stability of the fluid model.** Let $\kappa=b_{\max}/t_{b_{\max}}$ with batch-time parameters satisfying Assumption 1. Let $\lambda\ge 0$, $m_p>0$ and $m_d>0$ satisfy the load condition (eq. (36) = eq. (12))
--   $$
--   \lambda(m_p+m_d)<\frac{b_{\max}}{t_{b_{\max}}}.
--   $$
--   Then there is a time $\delta>0$ such that every work-conserving fluid model solution $(B_f,F_f,W_f,Z_f)_{f\in\{p,d\}}$ satisfies $Z_p(t)=Z_d(t)=0$ for all $t\ge\delta$, provided its request levels are nonnegative ($Z_p(t),Z_d(t)\ge 0$ for $t\ge 0$) and $Z_p(0)+Z_d(0)\le 1$. Here a work-conserving fluid model solution is one that satisfies eqs. (45)–(49) and (52), as in Definition 13.
--
--   This is the stability of the fluid model (Definition 14) under the load condition. In the fluid-limit approach it is the deterministic step from which positive recurrence of the stochastic model is derived.
--
--   **Formalization Note** The scheduling algorithm enters the fluid model only through eq. (52), so the statement quantifies over all work-conserving fluid model solutions. The time $\delta$ is chosen before the solution, as in Definition 14.
--
--   Differences from the source:
--   - correction: fluid model solutions satisfying (45)–(49), (52) → in addition $Z_p(t),Z_d(t)\ge 0$ for $t\ge 0$; reason: without it the claim is false. Take $m_p=m_d=1$, $\lambda=1/4$, $\kappa=1$, $Z(0)=0$, $B_p(t)=t$ and $B_d\equiv 0$. This satisfies (45)–(49) and (52), with $Z_p(t)=-3t/4$ and $Z_d(t)=t\ne 0$. The fluid limits it is meant for are nonnegative by (39)–(42)
--   - encoding: "under any work-conserving, K-FCFS algorithm" → every work-conserving fluid model solution (Definition 13); reason: the algorithm appears in the fluid model only through (52)
--   - encoding: eq. (48) $F_f(t)=\frac1{m_f}B_f(f)$ → $F_f(t)=B_f(t)/m_f$; reason: typo; (60) on p. 41 has $B_f(t)$
--   - encoding: Definition 12, "the solution is differentiable at time $t$" → each of the eight component functions is differentiable at $t>0$; reason: same condition, componentwise
--   - encoding: functions on $\mathbb R_+$ → functions on $\mathbb R$ with the equations imposed on $[0,\infty)$; reason: values at negative times are unconstrained and irrelevant; one-sided issues do not arise since regular points are $t>0$
--   - generalization: $\lambda=E[a_1]$, $m_f=E[v_f(1)]\ge 1$ → arbitrary reals $\lambda\ge 0$, $m_p,m_d>0$; reason: specializes to the model's means
--   - encoding: $a,c\ge 0$ real, $b_0\mid b_{\max}$ → $a,c\in\mathbb N$ and $1\le b_0$, $1\le b_{\max}$, $1\le t_{b_{\max}}$; reason: integer slots force integer $a,c$, and the other conditions only exclude undefined cases
-- source:
--   Dai, Deng, Li & Peng, Throughput-Optimal Scheduling Algorithms for LLM Inference and AI Agents, arXiv:2504.07347v3, p. 40, Proposition 15; fluid model (45)–(49), (52) and Definitions 12–14, pp. 39–40; load condition (36), p. 36

import Mathlib
import Definitions.Def_LLMThroughput_TokenBudget_Model
import Definitions.Def_LLMThroughput_TokenBudget_Fluid

namespace LLMThroughput.TokenBudget

theorem proposition_15 (P : Params) (hP : P.Valid) (lam mp md : ℝ) (hlam : 0 ≤ lam)
    (hmp : 0 < mp) (hmd : 0 < md)
    (hload : lam * (mp + md) < (P.bmax : ℝ) / (P.t P.bmax : ℝ)) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ s : FluidPath, IsWCFluidSolution lam mp md ((P.bmax : ℝ) / (P.t P.bmax : ℝ)) s →
        (∀ t, 0 ≤ t → 0 ≤ s.Zp t ∧ 0 ≤ s.Zd t) →
        s.Zp 0 + s.Zd 0 ≤ 1 →
        ∀ t, δ ≤ t → s.Zp t = 0 ∧ s.Zd t = 0 := by sorry

end LLMThroughput.TokenBudget
