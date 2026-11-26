-- Prove2me | Theorems.Thm_LefebvreVariations_bb4_halts_within_107_or_never
-- name    : LefebvreVariations.bb4_halts_within_107_or_never
-- status  : Open
-- author  : @Secousses
-- created : 2026-11-26T21:11:41.020939+00:00
-- url     : https://prove2.me/theorems/52f3b5eb-574d-5fae-aa61-fe4096ce3d36
-- title:
--   Lefebvre's variations, No. 164 — on a theme by bbchallenge: every 4-state two-symbol Turing machine either never halts or halts within 107 steps
-- statement:
--   Let $M$ be a Turing machine with $4$ states and two symbols, with transition table $\delta(q,b)=(w,\mathrm{right},q')$ where $q'$ is a state or the halting state. Run $M$ from state $0$ on the all-blank tape, head at position $0$. Then either $M$ never halts, or $M$ halts after at most $107$ transitions (the final halting transition included):
--   $$\bigl(\forall t,\ \mathrm{state}_t\neq\mathrm{halt}\bigr)\ \lor\ \bigl(\exists t\le 107,\ \mathrm{state}_t=\mathrm{halt}\bigr).$$
--   This is the value $S(4)=107$ of Rado's shift function, the maximum number of steps of a halting $4$-state two-symbol machine.
--
--   It is the $4$-state analogue of the platform's BB5.halt_le_0RB and BB5.halt_le_1RB (five states, bound $47{,}176{,}870$).
--
--   **Formalization Note** The run is encoded by sequences $\mathrm{st}:\mathbb N\to\mathrm{Option}(\mathrm{Fin}\,4)$ (\texttt{none} = halted), $\mathrm{tp}:\mathbb N\to\mathbb Z\to\mathrm{Bool}$ and $\mathrm{hd}:\mathbb N\to\mathbb Z$, constrained by the transition table only while the machine has not halted. The write bit and the move bit (\texttt{true} = right) are read from $\delta$. Halting at time $t$ means $\mathrm{st}\,t=\texttt{none}$.
--
--   **Why this is a variation.** This is a variation on the open platform problem BB5.halt_le_0RB (every 5-state machine with first transition 0RB halts within 47,176,870 steps or never). It plays the same statement, without the first-transition restriction, at 4 states, the case S(4)=107. The five-state statement remains open on the platform; no formal link between the two is claimed.
--
--   **Attribution.** This statement belongs to *Lefebvre's variations*, a series proposed by Erwan Lefebvre: each variation plays an open problem of the platform at its first non-trivial size, so that it can be settled and then reused to attack the open problem itself.
-- source:
--   A. H. Brady, The determination of the value of Rado's noncomputable function Sigma(k) for four-state Turing machines, Math. Comp. 40 (1983), 647-665 (Sigma(4)=13, S(4)=107; confirmed via search at ams.org/mcom/1983-40-162).

import Mathlib

namespace LefebvreVariations

/-- The 4-state, 2-symbol Busy Beaver shift function: every 4-state, 2-symbol Turing machine
started on the blank tape in state `0` either never halts or halts after at most 107 transitions
(the halting transition is counted). `δ q b = (write, moveRight, next)` with `next = none` meaning
halt; `st t = none` means the machine has halted after `t` transitions; the recurrence only
constrains the run while it has not halted.
Source: A. H. Brady, Math. Comp. 40 (1983) 647-665 (S(4)=107). -/
theorem bb4_halts_within_107_or_never
    (δ : Fin 4 → Bool → Bool × Bool × Option (Fin 4))
    (st : ℕ → Option (Fin 4)) (tp : ℕ → ℤ → Bool) (hd : ℕ → ℤ)
    (st0 : st 0 = some 0) (tp0 : ∀ z, tp 0 z = false) (hd0 : hd 0 = 0)
    (step : ∀ t q, st t = some q →
      st (t + 1) = (δ q (tp t (hd t))).2.2 ∧
      tp (t + 1) = Function.update (tp t) (hd t) (δ q (tp t (hd t))).1 ∧
      hd (t + 1) = if (δ q (tp t (hd t))).2.1 then hd t + 1 else hd t - 1) :
    (∀ t, st t ≠ none) ∨ ∃ t, t ≤ 107 ∧ st t = none := by
  sorry

end LefebvreVariations
