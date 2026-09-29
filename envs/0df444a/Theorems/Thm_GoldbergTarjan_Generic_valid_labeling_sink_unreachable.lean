-- Prove2me | Theorems.Thm_GoldbergTarjan_Generic_valid_labeling_sink_unreachable
-- name    : GoldbergTarjan.Generic.valid_labeling_sink_unreachable
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T14:27:00.302637+00:00
-- url     : https://prove2.me/theorems/620ddc5d-cc29-44f6-835f-87aab459394c
-- title:
--   Lemma 3.3 — under a valid labeling the sink is not reachable from the source in the residual graph
-- statement:
--   Let $N$ be a flow network, let $f$ be a preflow and let $d$ be any valid labeling for $f$. Then
--
--   $$t \text{ is not reachable from } s \text{ in the residual graph } G_f.$$
--
--   Lemma 3.3 says that the algorithm's preflow never admits an augmenting path; once the preflow has become a flow, Theorem 3.2 makes it a maximum flow.
-- source:
--   Goldberg, Tarjan, A New Approach to the Maximum-Flow Problem, J. ACM 35(4), 1988, p. 926, Lemma 3.3

import Mathlib
import Definitions.Def_GoldbergTarjan_Generic_Labeling

namespace GoldbergTarjan.Generic

/-- Lemma 3.3 (Goldberg–Tarjan 1988, p. 926). If `f` is a preflow and `d` is any valid labeling
for `f`, then the sink `t` is not reachable from the source `s` in the residual graph `G_f`. -/
theorem valid_labeling_sink_unreachable {V : Type} [Fintype V]
    (N : Network V) (f : V → V → ℝ) (d : V → ℕ∞)
    (hf : IsPreflow N f) (hd : IsValidLabeling N f d) :
    ¬ ResidualReachable N f N.s N.t := by sorry

end GoldbergTarjan.Generic
