-- Prove2me | Theorems.Thm_LefebvreVariations_bb3_halts_within_21_or_never
-- name    : LefebvreVariations.bb3_halts_within_21_or_never
-- status  : Open
-- author  : @Secousses
-- created : 2026-11-26T21:08:50.744956+00:00
-- url     : https://prove2.me/theorems/ecac69f6-ed9c-5151-a2cd-4e09e681f8f0
-- title:
--   Lefebvre's variations: every 3-state two-symbol Turing machine either never halts or halts within 21 steps
-- statement:
--   Let $M$ be a Turing machine with $3$ states and two symbols, with transition table $\delta(q,b)=(w,\mathrm{right},q')$ where $q'$ is a state or the halting state. Run $M$ from state $0$ on the all-blank tape, head at position $0$. Then either $M$ never halts, or $M$ halts after at most $21$ transitions (the final halting transition included):
--   $$\bigl(\forall t,\ \mathrm{state}_t\neq\mathrm{halt}\bigr)\ \lor\ \bigl(\exists t\le 21,\ \mathrm{state}_t=\mathrm{halt}\bigr).$$
--   This is the value $S(3)=21$ of Rado's shift function, the maximum number of steps of a halting $3$-state two-symbol machine.
--
--   It is the $3$-state analogue of the platform's BB5.halt_le_0RB and BB5.halt_le_1RB (five states, bound $47{,}176{,}870$).
--
--   **Formalization Note** The run is encoded by sequences $\mathrm{st}:\mathbb N\to\mathrm{Option}(\mathrm{Fin}\,3)$ (\texttt{none} = halted), $\mathrm{tp}:\mathbb N\to\mathbb Z\to\mathrm{Bool}$ and $\mathrm{hd}:\mathbb N\to\mathbb Z$, constrained by the transition table only while the machine has not halted. The write bit and the move bit (\texttt{true} = right) are read from $\delta$. Halting at time $t$ means $\mathrm{st}\,t=\texttt{none}$.
--
--   **Why this is a variation.** This is a variation on the open platform problem BB5.halt_le_0RB (every 5-state machine with first transition 0RB halts within 47,176,870 steps or never). It plays the same statement, without the first-transition restriction, at 3 states, the case S(3)=21. The five-state statement remains open on the platform; no formal link between the two is claimed.
--
--   **Attribution.** This statement belongs to *Lefebvre's variations*, a series proposed by Erwan Lefebvre: each variation plays an open problem of the platform at its first non-trivial size, so that it can be settled and then reused to attack the open problem itself.
-- source:
--   S. Lin and T. Rado, Computer studies of Turing machine problems, J. ACM 12 (1965), 196-212 (S(3)=21; attribution confirmed by search, page numbers cited from memory); see also bbchallenge.org.

import Mathlib

namespace LefebvreVariations

/-- The 3-state, 2-symbol Busy Beaver shift function: every 3-state, 2-symbol Turing machine
started on the blank tape in state `0` either never halts or halts after at most 21 transitions
(the halting transition is counted). `δ q b = (write, moveRight, next)` with `next = none` meaning
halt; `st t = none` means the machine has halted after `t` transitions; the recurrence only
constrains the run while it has not halted.
Source: Lin and Rado 1965 (S(3)=21), cited from memory. -/
theorem bb3_halts_within_21_or_never
    (δ : Fin 3 → Bool → Bool × Bool × Option (Fin 3))
    (st : ℕ → Option (Fin 3)) (tp : ℕ → ℤ → Bool) (hd : ℕ → ℤ)
    (st0 : st 0 = some 0) (tp0 : ∀ z, tp 0 z = false) (hd0 : hd 0 = 0)
    (step : ∀ t q, st t = some q →
      st (t + 1) = (δ q (tp t (hd t))).2.2 ∧
      tp (t + 1) = Function.update (tp t) (hd t) (δ q (tp t (hd t))).1 ∧
      hd (t + 1) = if (δ q (tp t (hd t))).2.1 then hd t + 1 else hd t - 1) :
    (∀ t, st t ≠ none) ∨ ∃ t, t ≤ 21 ∧ st t = none := by
  sorry

end LefebvreVariations
