-- Prove2me | Theorems.Thm_LinuxRV_monitor_correct
-- name    : LinuxRV.monitor_correct
-- status  : Open
-- author  : @kmehltretter82
-- created : 2026-11-22T20:12:04.933696+00:00
-- url     : https://prove2.me/theorems/450ab57e-8e55-47cd-a81e-7689b13096f4
-- title:
--   Trace correctness and first undefined transition
-- statement:
--   For every finite trace, the generated monitor succeeds at precisely the final state reached by the generator. It reports index $i$, state $q$, and event $e$ precisely when the first $i$ events reach $q$ and the next event is $e$ with an undefined transition.
-- source:
--   de Oliveira, Cucinotta and de Oliveira, Efficient Formal Verification for the Linux Kernel (SEFM 2019), §§2 and 4, Figs. 4–6, 8. https://doi.org/10.1007/978-3-030-30446-1_17

import Definitions.Def_LinuxRV_TransitionTable
open RamadgeWonham.Shared

namespace LinuxRV
theorem monitor_correct {α : Type} {n m : Nat} (G : Generator α)
    (states : G.Q ≃ Fin n) (events : α ≃ Fin m) (trace : List α) :
    (∀ q, monitor G states events trace = .ok (states q) ↔ G.run trace = some q) ∧
    (∀ i q e, monitor G states events trace = .error (i, states q, events e) ↔
      ∃ pre post, trace = pre ++ e :: post ∧ pre.length = i ∧
        G.run pre = some q ∧ G.δ e q = none) := by sorry
end LinuxRV
