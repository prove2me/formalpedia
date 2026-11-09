-- Prove2me | Theorems.Thm_MatchingDelays_Linear_offline_equivalence
-- name    : MatchingDelays.Linear.offline_equivalence
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:53:30.937571+00:00
-- url     : https://prove2.me/theorems/75c4f685-93ed-4756-b4d0-94a9c778b4d9
-- title:
--   Lemma 2.1 — Offline optimum in the time-expanded pseudometric
-- statement:
--   Let $I$ consist of an even number $n\ge2$ of requests in an arbitrary metric space, with finite nonnegative arrival times. Let $\operatorname{OPT}_{\mathrm{time}}$ be the infimum of feasible timed-schedule costs and $\operatorname{OPT}_{d}$ the minimum perfect-pairing weight for $d(u,v)=d_0(x_u,x_v)+|a_u-a_v|$. Then
--   $$\operatorname{OPT}_{\mathrm{time}}=\operatorname{OPT}_{d}.$$
--   The feasible timed-cost set is nonempty and bounded below, and both sides are attained by a feasible schedule and a perfect pairing, respectively.
--
--   This identifies the original offline objective with an independently defined finite pairing problem.
--
--   Differences from the source:
--   - encoding: requests labeled [n] in continuous real time → arrival-ranked Fin n input, batched simultaneous arrivals, and natural-number microsteps with continuous interpolation; reason: relabeling preserves all inputs and ties; microsteps do not discretize time, and maturations causing no action may be omitted
--   - encoding: optimal schedule cost equals minimum perfect-pairing weight → independent real infima together with nonemptiness, lower boundedness and both attainments; reason: the explicit side conclusions justify totalized infima without adding a hypothesis
-- source:
--   Ahmadian, Chawla, Kumar, Purohit, and Zhang, STOC 2027 submission #482 (October 2026), Lemma 2.1, printed p.5 / PDF p.6. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/482.pdf

import Mathlib
import Definitions.Def_MatchingDelays_Linear_Instance

set_option autoImplicit false
open scoped BigOperators
open Classical
noncomputable section

namespace MatchingDelays.Linear

variable {n : ℕ} {X : Type*} [MetricSpace X]

theorem offline_equivalence (I : Instance n X) (hn : ValidSize n) :
    offlineOpt I = pairingOpt I ∧
    (timedCosts I).Nonempty ∧ BddBelow (timedCosts I) ∧
    (∃ M T, IsPairing n M ∧ FeasibleTimes I M T ∧ scheduleCost I M T = offlineOpt I) ∧
    (∃ M, IsPairing n M ∧ pairingCost I M = pairingOpt I) := by sorry

end MatchingDelays.Linear
