-- Prove2me | Theorems.Thm_GoldbergTarjan_FIFO_pass_count_le
-- name    : GoldbergTarjan.FIFO.pass_count_le
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T14:37:09.284686+00:00
-- url     : https://prove2.me/theorems/a47e4853-7d48-45ec-a8a3-b5103a4a3038
-- title:
--   Lemma 4.3 — the first-in, first-out algorithm makes at most $4n^2$ passes over the queue
-- statement:
--   Let $n = |V|$. Pass one over the queue consists of the discharges of the vertices added to the queue during the initialization. Pass $i+1$ consists of the discharges of the vertices added to the queue during pass $i$. In every run of the first-in, first-out algorithm, $$\#\{\text{passes over the queue}\} \le 4n^2.$$
--
--   Within a pass each vertex is discharged at most once, so this bound turns into a bound on the number of discharges and, with Corollary 4.4, on the number of nonsaturating pushes.
--
--   **Formalization Note** The passes made by a run of $K$ discharges are counted as the largest pass number of a discharged queue entry. The pass number of an entry is propagated as in the definition: $1$ at initialization, and $i+1$ for every vertex added during a discharge of pass $i$.
-- source:
--   Goldberg, Tarjan, A New Approach to the Maximum-Flow Problem, J. ACM 35(4), 1988, p. 930, Lemma 4.3

import Mathlib
import Definitions.Def_GoldbergTarjan_FIFO_Network
import Definitions.Def_GoldbergTarjan_FIFO_PushRelabel
import Definitions.Def_GoldbergTarjan_FIFO_Algorithm
import Definitions.Def_GoldbergTarjan_FIFO_Counts

namespace GoldbergTarjan.FIFO

/-- Lemma 4.3 (Goldberg–Tarjan 1988, p. 930): the number of passes over the queue made by the
first-in, first-out algorithm is at most `4n²`, where `n = |V|`. Pass one consists of the
discharges of the vertices added to the queue during the initialization, and pass `i + 1` of the
discharges of the vertices added during pass `i`; the passes made by the first `K` discharges
number the largest pass tag of a discharged entry. -/
theorem pass_count_le {V : Type} [Fintype V] [DecidableEq V]
    (N : Network V) (L : V → List V) (K : ℕ) (S : ℕ → State V) (J : ℕ → ℕ)
    (hrun : IsFIFORun N L K S J) :
    passCount K S ≤ 4 * Fintype.card V ^ 2 := by sorry

end GoldbergTarjan.FIFO
