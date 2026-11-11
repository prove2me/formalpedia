-- Prove2me | Theorems.Thm_IntervalExplore_KT1_remark_1
-- name    : IntervalExplore.KT1.remark_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:10:42.614964+00:00
-- url     : https://prove2.me/theorems/fcea0be7-e87a-4454-813c-7b4f1ca42f01
-- title:
--   Remark 1 — common spanning tree extension and transfer
-- statement:
--   Let $T\ge1$ and let a finite dynamic graph be $T$-interval-connected. There exists a spanning tree $H$ of its underlying graph present in snapshots $0,\ldots,T-1$. Add $H$ to every snapshot from time $T$ onward, producing $\widetilde G_t$. Then
--   $$
--   H\subseteq\widetilde G_t\quad\text{for every }t,\qquad
--   \widetilde G\text{ is }T\text{-interval-connected}.
--   $$
--   For every deterministic observation-only algorithm and the same identifiers, ports and starting vertex, the two executions have identical states, observations, histories and decisions at every time $t<T$. Consequently, exploration and termination by time $T-1$ in the extended schedule imply the same in the original schedule.
--
--   This is the schedule reduction in Remark 1. The later charge bound and the choice of the sufficiently large window constant are asserted by the goal theorem, rather than assumed here.
--
--   Differences from the source:
--   - generalization: the window τ(n,m) and GreedyExp1 → any positive window T and any deterministic observation-only algorithm; reason: the indistinguishability argument depends only on equality of snapshots before T and specializes to the stated window and algorithm
--   - reading: the remark also states that the analysis yields an O-bound at most τ(n,m)-1 for sufficiently large c → this item states the structural reduction and transfer, while the goal carries the full exploration bound; reason: the last two sentences invoke the subsequent analysis; no exploration bound is assumed in the reduction
-- source:
--   Yuichi Sudo, Naoki Kitamura, Masahiro Shibata, Junya Nakamura, Sébastien Tixeuil, Toshimitsu Masuzawa, Koichi Wada, STOC 2027 submission #1589 (October 2026), Remark 1, p.6 (PDF p.7)

import Definitions.Def_IntervalExplore_KT1_Execution

set_option autoImplicit false

namespace IntervalExplore.KT1

/-- Remark 1, p.6 (PDF p.7): common-tree extension and indistinguishability.
The O-bound and sufficiently-large-c arithmetic remain in Theorem 2. -/
theorem remark_1 {V : Type} [Fintype V] [DecidableEq V] (W : World V)
    (T : ℕ) (hT : IntervalConnected W.dynamic T) :
    ∃ H : SimpleGraph V, H.IsTree ∧ ∃ hH : H ≤ W.graph,
      (∀ t < T, H ≤ W.dynamic.snapshot t) ∧
      (∀ t, H ≤ (extendWorld W H hH T).dynamic.snapshot t) ∧
      IntervalConnected (extendWorld W H hH T).dynamic T ∧
      ∀ A : Alg,
        (∀ t < T, state W A t = state (extendWorld W H hH T) A t ∧
          history W A t = history (extendWorld W H hH T) A t ∧
          observe W t (state W A t).position (state W A t).incoming =
            observe (extendWorld W H hH T) t
              (state (extendWorld W H hH T) A t).position
              (state (extendWorld W H hH T) A t).incoming ∧
          decision W A t = decision (extendWorld W H hH T) A t) ∧
        (ExploresWithin (extendWorld W H hH T) A (T - 1) → ExploresWithin W A (T - 1)) := by sorry

end IntervalExplore.KT1
