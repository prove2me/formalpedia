-- Prove2me | Theorems.Thm_NetworkedMarkets_Relaxation_theorem_1
-- name    : NetworkedMarkets.Relaxation.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T17:25:37.399613+00:00
-- url     : https://prove2.me/theorems/5960cd0d-c7dd-4769-9004-12b215202ec4
-- title:
--   Theorem 1, p. 13 — the convex program (7) is a tight relaxation of the revenue problem (3), and optimal fees are those solving the linear system (8)
-- statement:
--   Consider a networked market satisfying the standing assumptions of §2 and Assumptions 1–2, and let $(\bar x,\bar q^s,\bar q^b)$ be an optimal solution of the relaxation (7). Then:
--
--   1. **(i)** The revenue problem (3) has an optimal solution, its optimal value is $V_{opt}=\tilde V_{opt}=h(\bar q^s,\bar q^b)$, and every optimal solution of (3) has supply-demand vector $(\bar q^s,\bar q^b)$.
--   2. **(ii)** Let $(\gamma,\mu)\in\Gamma\times\mathcal U$ with $\gamma^s_i<1$ for all $i$, and set $\tilde\gamma^s_i=\frac{1}{1-\gamma^s_i}$, $\tilde\mu^s_i=\frac{\mu^s_i}{1-\gamma^s_i}$, $\tilde\gamma^b_j=\frac{1}{1+\gamma^b_j}$, $\tilde\mu^b_j=\frac{\mu^b_j}{1+\gamma^b_j}$. Then $(\gamma,\mu)$ is an optimal commission-subscription pair if and only if there are a price vector $p\in\mathbb R^{\mathcal S}_+$ and an optimal flow $x$ of (7) with supply-demand vector $(\bar q^s,\bar q^b)$ such that
--   $$\begin{aligned}
--   &p_i-\tilde\mu^s_i-F^{-1}_{s_i}(\bar q^s_i/s_i)\,\tilde\gamma^s_i=0 \ \ (\bar q^s_i>0), \qquad p_i-\tilde\mu^s_i\le 0\ \ (\bar q^s_i=0),\\
--   &p_i+\tilde\mu^b_j+c_i\tilde\gamma^b_j-F^{-1}_{b_j}(1-\bar q^b_j/b_j)\,\tilde\gamma^b_j=0\ \ ((i,j)\in E,\ x_{ij}>0),\\
--   &p_i+\tilde\mu^b_j+c_i\tilde\gamma^b_j-F^{-1}_{b_j}(1-\bar q^b_j/b_j)\,\tilde\gamma^b_j\ge0\ \ ((i,j)\in E,\ x_{ij}=0),\\
--   &\tilde\gamma^s_i\ge1,\ \tilde\mu^s_i\ge0,\ p_i\ge0,\qquad 0\le\tilde\gamma^b_j\le1,\ \tilde\mu^b_j\ge0.
--   \end{aligned}$$
--
--   The nonconvex revenue problem is thus solved by a convex program, and the optimal fees are exactly the solutions of a system that is linear in $(p,\tilde\gamma,\tilde\mu)$.
--
--   **Formalization Note.** (1) The printed part (ii) fixes the flow $\bar x$ in (8c)–(8d). Since the objective of (7) depends only on $(q^s,q^b)$, optimal flows are not unique, and the fixed-flow reading is false: in a two-seller, two-buyer complete market ($s=b=(1,1)$, sellers uniform on $[0,1]$, buyers uniform on $[0,10]$, $c=(0.1,0)$) an optimal pair solves (8) for one optimal flow but not for another one obtained by shifting $0.1$ units around a cycle. The statement here asks for *some* optimal flow of (7) with the given supply-demand vector, which is the reading the paper's proof supports. (2) The sentence "The optimal commission-subscription vector is not unique" is a remark that the proof illustrates by an example; it is not posed. (3) "Optimal" for $(\gamma,\mu)$ means that some competitive equilibrium under $(\gamma,\mu)$ attains the maximum of (3); by Corollary 1 this is the paper's $V(\gamma,\mu)=V_{opt}$. (4) The maximum of (3) is stated as attained (greatest element of the set of feasible revenues).
-- source:
--   Birge, Candogan, Chen, Saban, Optimal Commissions and Subscriptions in Networked Markets, SSRN abstract 3259716 (version of 2019-09-13), p. 13, Theorem 1, (8a)–(8f); proof in EC.3.1, pp. ec38–ec44 (PDF 82–88)

import Mathlib
import Definitions.Def_NetworkedMarkets_Relaxation_Setting

open Filter Topology

namespace NetworkedMarkets.Relaxation

theorem theorem_1 {S B : Type*} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
    (M : Market S B) (hM : M.Standing)
    (xbar : S → B → ℝ) (qsbar : S → ℝ) (qbbar : B → ℝ) (hopt : M.IsOpt7 xbar qsbar qbbar) :
    -- (i) optimal solutions to (3) exist and achieve V_opt = Ṽ_opt
    IsGreatest M.Value3 (M.h qsbar qbbar) ∧
    -- (i) every optimal solution to (3) has supply-demand vector (q̄ˢ, q̄ᵇ)
    (∀ (f : Fees S B) (p : S → ℝ) (x : S → B → ℝ) (qs : S → ℝ) (qb : B → ℝ),
      M.Feas3 f p x qs qb → M.rev f p x = M.h qsbar qbbar → qs = qsbar ∧ qb = qbbar) ∧
    -- (ii) characterization of the optimal pairs with γˢ < 1, via (8a)–(8f)
    (∀ f : Fees S B, f.InGammaU → (∀ i, f.γs i < 1) →
      (M.IsOptimalFees f ↔
        ∃ (p : S → ℝ) (x : S → B → ℝ), M.IsOpt7 x qsbar qbbar ∧ M.Sys8 f p x qsbar qbbar)) := by sorry

end NetworkedMarkets.Relaxation
