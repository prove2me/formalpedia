-- Prove2me | Theorems.Thm_NetworkedMarkets_Relaxation_theorem_1_i
-- name    : NetworkedMarkets.Relaxation.theorem_1_i
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T17:25:32.101617+00:00
-- url     : https://prove2.me/theorems/8cd0960d-f521-4b18-b439-1ff69b5c68b7
-- title:
--   Theorem 1(i), p. 13 — (7) is a tight relaxation of (3): the revenue maximum exists, equals Ṽ_opt, and forces the supply-demand vector (q̄^s, q̄^b)
-- statement:
--   Under the standing assumptions and Assumptions 1–2, let $(\bar x,\bar q^s,\bar q^b)$ be an optimal solution of the relaxation (7). Then:
--
--   1. the revenue problem (3) has an optimal solution, and its optimal value equals that of (7):
--   $$V_{opt}=\max\{\text{revenue (3a) of a feasible solution of (3)}\}=h(\bar q^s,\bar q^b)=\tilde V_{opt};$$
--   2. every optimal solution $(\gamma,\mu,p,x,q^s,q^b)$ of (3) has supply-demand vector $(q^s,q^b)=(\bar q^s,\bar q^b)$.
--
--   Although the revenue problem (3) is nonconvex, its value and its optimal supply-demand vector are those of the convex program (7).
--
--   **Formalization Note.** "Optimal solutions to (3) exist and achieve $V_{opt}=\tilde V_{opt}$" is stated as: $h(\bar q^s,\bar q^b)$ is the greatest element of the set of revenues of feasible solutions of (3) (so the maximum is attained). An optimal solution of (3) is a feasible one whose revenue equals that maximum.
-- source:
--   Birge, Candogan, Chen, Saban, Optimal Commissions and Subscriptions in Networked Markets, SSRN abstract 3259716 (version of 2019-09-13), p. 13, Theorem 1(i)

import Mathlib
import Definitions.Def_NetworkedMarkets_Relaxation_Setting

open Filter Topology

namespace NetworkedMarkets.Relaxation

theorem theorem_1_i {S B : Type*} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
    (M : Market S B) (hM : M.Standing)
    (xbar : S → B → ℝ) (qsbar : S → ℝ) (qbbar : B → ℝ) (hopt : M.IsOpt7 xbar qsbar qbbar) :
    IsGreatest M.Value3 (M.h qsbar qbbar) ∧
      ∀ (f : Fees S B) (p : S → ℝ) (x : S → B → ℝ) (qs : S → ℝ) (qb : B → ℝ),
        M.Feas3 f p x qs qb → M.rev f p x = M.h qsbar qbbar → qs = qsbar ∧ qb = qbbar := by sorry

end NetworkedMarkets.Relaxation
