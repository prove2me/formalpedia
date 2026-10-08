-- Prove2me | Theorems.Thm_ObliviousRAM_LowerBound_card_satisfied_le
-- name    : ObliviousRAM.LowerBound.card_satisfied_le
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:09:58.550216+00:00
-- url     : https://prove2.me/theorems/ee42c93d-6a51-47b6-b348-9962d888594e
-- title:
--   §6, p. 470 — corrected count of requests served by a fixed run
-- statement:
--   Fix a run $a$ of $q$ accesses, a hand capacity $b$, and $t$ request rounds. The number of request sequences that this run legally satisfies is bounded by
--
--   $$
--   |\{r:a\models r\}|\le \operatorname{multichoose}(q,t)\,b^t.
--   $$
--
--   This bounds the request sequences associated with a single hidden action history, retaining the paper's non-strict round-end indices.
--
--   **Formalization Note** The printed proof says $b^q$ and footnote 29 offers $\binom qt b^t$; both fail when round ends repeat. With $m=b=q=2$ and $t=7$, a run that takes both balls serves all $2^7$ request sequences, exceeding $b^q=4$ while $\binom qt=0$. The formal bound uses `Nat.multichoose q t`, equal to $\binom{q+t-1}{t}$ when $q\ge1$, and is the corrected statement needed for Theorem 6.1. No legality hypothesis is needed: an illegal run satisfies no requests.
-- source:
--   Goldreich and Ostrovsky, Software protection and simulation on oblivious RAMs, J. ACM 43 (1996), p. 470, §6, proof of THEOREM 6.1 and footnote 29 (printed bounds corrected); https://doi.org/10.1145/233551.233553

import Mathlib
import Definitions.Def_ObliviousRAM_LowerBound_Game

namespace ObliviousRAM.LowerBound
open Classical

theorem card_satisfied_le {b m t : ℕ} (a : List (Action m)) :
    (Finset.univ.filter fun r : Fin t → Fin m => Satisfies b a r).card ≤
      Nat.multichoose a.length t * b ^ t := by sorry

end ObliviousRAM.LowerBound
