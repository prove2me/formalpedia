-- Prove2me | Theorems.Thm_LogicBenders_Generic_unbounded_of_dual_infeasible
-- name    : LogicBenders.Generic.unbounded_of_dual_infeasible
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:33:16.729113+00:00
-- url     : https://prove2.me/theorems/492b8194-c0d3-4225-ad7b-3e23cf26aa78
-- title:
--   Proof of Theorem 1, p. 9 — if the subproblem dual is infeasible, the subproblem is unbounded, and so (6) is unbounded
-- statement:
--   Let problem (6) be given by $S \subseteq D_x\times D_y$ and $f$, and let $\bar y \in D_y$. Suppose the subproblem dual (8) at $\bar y$ is infeasible: no real number $\beta$ satisfies $(x,\bar y)\in S \xrightarrow{D_x} f(x,\bar y)\ge\beta$. Then
--
--   1. the subproblem (7) is unbounded: for every real $M$ there is $x$ with $(x,\bar y)\in S$ and $f(x,\bar y) < M$;
--   2. problem (6) is unbounded: for every real $M$ there is $(x,y)\in S$ with $f(x,y) < M$.
--
--   This is the third clause of the proof of Theorem 1.
--
--   **Formalization Note.** "Infeasible" means that no *real* $\beta$ is feasible. The value $\beta = -\infty$ is always trivially feasible, so the infeasibility of the dual cannot be stated over the extended reals.
-- source:
--   Hooker & Ottosson, Logic-based Benders decomposition, revised manuscript (Nov. 2000), p. 9, proof of Theorem 1, third paragraph

import Mathlib
import Definitions.Def_LogicBenders_Generic_Setting

namespace LogicBenders.Generic

theorem unbounded_of_dual_infeasible {X Y : Type*} (S : Set (X × Y)) (f : X → Y → ℝ) (yb : Y)
    (h : ¬ ∃ β : ℝ, IsDualFeasible S f yb (β : EReal)) :
    (∀ M : ℝ, ∃ x : X, (x, yb) ∈ S ∧ f x yb < M) ∧ IsUnbounded S f := by sorry

end LogicBenders.Generic
