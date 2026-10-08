-- Prove2me | Theorems.Thm_LogicBenders_Generic_infeasible_of_master_infeasible
-- name    : LogicBenders.Generic.infeasible_of_master_infeasible
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:33:27.960457+00:00
-- url     : https://prove2.me/theorems/94c0287f-21eb-49c3-837a-e8f8f24fd3a2
-- title:
--   Proof of Theorem 1, p. 9 — because all Benders cuts are valid, infeasibility of the master problem implies that (6) is infeasible
-- statement:
--   Let problem (6) be given by $S \subseteq D_x\times D_y$ and $f$, and let $\beta^{(0)},\dots,\beta^{(k)} : D_y \to [-\infty,+\infty]$ be bounding functions satisfying (B1). If the master problem (9) with these cuts is infeasible, that is,
--   $$\max_{0\le j\le k}\beta^{(j)}(y) = +\infty \quad\text{for every } y \in D_y,$$
--   then (6) is infeasible: $S = \varnothing$.
--
--   This is the second clause of the proof of Theorem 1.
-- source:
--   Hooker & Ottosson, Logic-based Benders decomposition, revised manuscript (Nov. 2000), p. 9, proof of Theorem 1, second paragraph

import Mathlib
import Definitions.Def_LogicBenders_Generic_Setting

namespace LogicBenders.Generic

theorem infeasible_of_master_infeasible {X Y : Type*} (S : Set (X × Y)) (f : X → Y → ℝ)
    (cut : ℕ → Y → EReal) (k : ℕ) (hB1 : ∀ j ≤ k, ValidCut S f (cut j))
    (h : MasterInfeasible cut k) :
    S = ∅ := by sorry

end LogicBenders.Generic
