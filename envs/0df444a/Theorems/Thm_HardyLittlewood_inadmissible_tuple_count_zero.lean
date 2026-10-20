-- Prove2me | Theorems.Thm_HardyLittlewood_inadmissible_tuple_count_zero
-- name    : HardyLittlewood.inadmissible_tuple_count_zero
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-19T21:45:33.93443+00:00
-- url     : https://prove2.me/theorems/55a3d146-de49-4acc-bac1-c775a134661a
-- title:
--   Inadmissible tuples have a vanishing counting function
-- statement:
--   If the doubled offsets of m cover all residue classes modulo some prime q — at every base point p, since coverage is translation-invariant — then no base point carries an admissible prime constellation, and the counting function π_P(n) is zero for every n. This is the degenerate half of the conjecture: an inadmissible tuple has a zero count against a vanishing singular series.
-- source:
--   Formal Conjectures (2025), HardyLittlewood.lean, definition Nat.primeTupleCounting; the admissibility necessity of the prime k-tuple conjecture

import Mathlib
import Definitions.Def_HardyLittlewood_constellation
import Definitions.Def_HardyLittlewood_counting
import Definitions.Def_HardyLittlewood_series

namespace HardyLittlewood

/-- An inadmissible tuple contributes nothing to the count: if the residues of
the entries cover all of ZMod q for some prime q and every base point, then no
base point carries an admissible prime constellation, and the counting
function π_P(n) is identically zero. -/
theorem inadmissible_tuple_count_zero {k : ℕ} (m : Fin k.succ → ℕ)
    (q : ℕ) (hq : q.Prime)
    (h : ∀ p : ℕ, Function.Surjective (fun i : Fin k.succ => (p + 2 * m i : ZMod q)))
    (n : ℕ) : primeTupleCounting m n = 0 := by
  sorry

end HardyLittlewood
