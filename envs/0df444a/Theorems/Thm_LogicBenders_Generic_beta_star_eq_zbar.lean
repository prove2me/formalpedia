-- Prove2me | Theorems.Thm_LogicBenders_Generic_beta_star_eq_zbar
-- name    : LogicBenders.Generic.beta_star_eq_zbar
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:33:13.070336+00:00
-- url     : https://prove2.me/theorems/3b4822a3-04c8-4832-a2d6-286061e26eba
-- title:
--   Proof of Theorem 1, p. 9 — when the algorithm terminates at a master optimum (z̄, ȳ), the subproblem dual value β* equals z̄
-- statement:
--   Let problem (6) be given by $S$ and $f$, let $\beta^{(0)},\dots,\beta^{(k)}$ be bounding functions satisfying (B1), and let $(\bar z,\bar y)$ be an optimal solution, with value $\bar z$, of the master problem (9) with these cuts. Suppose the generic Benders algorithm terminates at $\bar y$, i.e. the While test of Figure 1 fails: the subproblem dual (8) at $\bar y$ has no feasible solution $\beta > \bar z$. Then the optimal value $\beta^*$ of the subproblem dual (8), and the optimal value of the subproblem (7), both equal $\bar z$:
--   $$\beta^* \;=\; \sup\{\beta : (x,\bar y)\in S \xrightarrow{D_x} f(x,\bar y)\ge\beta\} \;=\; \bar z \;=\; \inf_{(x,\bar y)\in S} f(x,\bar y).$$
--
--   This is the step "because the algorithm terminated with a finite solution, $\beta^* = \bar z$" of the proof of Theorem 1.
--
--   **Formalization Note.** The page assumes the master solution is finite; the equality holds without that assumption (including $\bar z = -\infty$), so the hypothesis is dropped and the statement is stronger. Both the dual value $\beta^*$ (the page's quantity) and the primal subproblem value are stated.
-- source:
--   Hooker & Ottosson, Logic-based Benders decomposition, revised manuscript (Nov. 2000), p. 9, proof of Theorem 1, fifth sentence; Figure 1 (While test), p. 9

import Mathlib
import Definitions.Def_LogicBenders_Generic_Setting

namespace LogicBenders.Generic

theorem beta_star_eq_zbar {X Y : Type*} (S : Set (X × Y)) (f : X → Y → ℝ)
    (cut : ℕ → Y → EReal) (k : ℕ) (hB1 : ∀ j ≤ k, ValidCut S f (cut j))
    (z : EReal) (yb : Y) (h : IsMasterOptimal cut k z yb)
    (hstop : ¬ ∃ β : EReal, IsDualFeasible S f yb β ∧ z < β) :
    subDualVal S f yb = z ∧ subVal S f yb = z := by sorry

end LogicBenders.Generic
