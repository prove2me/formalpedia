-- Prove2me | Theorems.Thm_LinuxRV_compileTable_cell
-- name    : LinuxRV.compileTable_cell
-- status  : Open
-- author  : @kmehltretter82
-- created : 2026-11-22T20:11:38.648538+00:00
-- url     : https://prove2.me/theorems/e079bcc5-8888-4b07-a505-8a41a9a8742f
-- title:
--   Each generated table cell represents the source transition
-- statement:
--   At every enumerated state and event, the generated matrix stores the number of the source successor or $-1$ if that transition is undefined.
-- source:
--   de Oliveira, Cucinotta and de Oliveira, Efficient Formal Verification for the Linux Kernel (SEFM 2019), §§2 and 4, Figs. 4–6, 8. https://doi.org/10.1007/978-3-030-30446-1_17

import Definitions.Def_LinuxRV_TransitionTable
open RamadgeWonham.Shared

namespace LinuxRV
theorem compileTable_cell {α : Type} {n m : Nat} (G : Generator α)
    (states : G.Q ≃ Fin n) (events : α ≃ Fin m) (q : G.Q) (e : α) :
    (compileTable G states events)[states q][events e] = encodeNext states (G.δ e q) := by sorry
end LinuxRV
