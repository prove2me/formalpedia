-- Prove2me | Theorems.Thm_OnlinePrimalDual_MTS_new_to_standard
-- name    : OnlinePrimalDual.MTS.new_to_standard
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-21T05:44:16.703706+00:00
-- url     : https://prove2.me/theorems/ea679103-39b9-4f9a-b416-ba3fb5e91b5c
-- title:
--   Lemma 6.2 — new-model solutions are standard-model solutions at cost ≤2× (milestone)
-- statement:
--   Any new-model solution (given by its phases `s`, actual service `w` with `w i ≤ d(s i)` per
--   phase) is, on the same trajectory, a standard-model solution whose cost is at most twice
--   `costNewPhases ws s`.
-- source:
--   Buchbinder & Naor, The Design of Competitive Online Algorithms via a Primal-Dual Approach, FnT TCS 2009, p. 145, Lemma 6.2

import Mathlib
import Definitions.Def_OnlinePrimalDual_MTS_WeightedStar
import Definitions.Def_OnlinePrimalDual_MTS_WeightedStar_d
import Definitions.Def_OnlinePrimalDual_MTS_costStandard
import Definitions.Def_OnlinePrimalDual_MTS_costNewPhases

namespace OnlinePrimalDual.MTS

/-- **Lemma 6.2** (p. 145, PDF p. 56, milestone). Any new-model solution, given by its `k`
phases (`s`, the state visited during each phase; `w`, the service actually accumulated during
that phase, necessarily `≤ d(s i)` since a phase is *defined* to end once accumulated service
reaches `d(s i)`, p. 144), is *also* a legal standard-model solution on the very same trajectory
(no transformation needed — "We run the solution `S` in the standard MTS model", p. 145), whose
standard-model cost is at most twice its new-model cost `costNewPhases`. The book's proof splits
this into two termwise bounds: "the cost of serving the requests in the standard MTS model is no
more than the cost of serving the requests in the new model" (`w i ≤ d(s i) = ` this phase's
`costNewPhases` contribution) and "the transition cost of solution `S` in the standard model is
no more than the service cost of `S` in the new model" (`d(s i) ≤ d(s i)`, via the pairing "the
cost `d(i)` of leaving the state can be charged to the service cost of the corresponding phase
that just ended, which is also exactly `d(i)`"); summed, `∑(w i + d(s i)) ≤ ∑2·d(s i)`. Combined
with Lemma 6.1: "a `c`-competitive algorithm in the new MTS model implies a `4c`-competitive
algorithm in the standard MTS model" (p. 145), the chapter's stated corollary of both lemmas
together, not separately formalized here. -/
theorem new_to_standard {V : Type*} {k : ℕ} (ws : WeightedStar V)
    (s : Fin k → V) (w : Fin k → ℝ) (hw_le : ∀ i, w i ≤ ws.d (s i)) :
    costStandard ws s w ≤ 2 * costNewPhases ws s := by sorry

end OnlinePrimalDual.MTS
