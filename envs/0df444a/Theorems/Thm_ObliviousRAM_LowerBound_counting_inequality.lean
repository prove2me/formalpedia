-- Prove2me | Theorems.Thm_ObliviousRAM_LowerBound_counting_inequality
-- name    : ObliviousRAM.LowerBound.counting_inequality
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:10:18.00799+00:00
-- url     : https://prove2.me/theorems/a2cef94e-d58c-44e8-9018-3f304a8244bb
-- title:
--   §6, p. 470 — corrected counting inequality for every visible run
-- statement:
--   Let $P$ be a correct oblivious randomized player for $t$ rounds, $m$ balls, and hand capacity $b$. For any request sequence and any positive-probability run $a$ of length $q$,
--
--   $$
--   m^t\le (b+2)^q\operatorname{multichoose}(q,t)b^t.
--   $$
--
--   The left side counts all request sequences; the right side bounds those served by the hidden histories compatible with the run's visible pattern. This is the counting statement used to obtain the logarithmic lower bound.
--
--   **Formalization Note** The printed proof instead gives $b^q(b+2)^q>m^t$ and infers $q>t\log_{b(b+2)}m$. Both fail for $m=b=q=2$, $t=7$, when a two-access oblivious run serves all $128$ requests but the printed product is $64$. The displayed weak inequality uses the corrected fixed-run count and keeps the paper's non-strict round-end convention.
-- source:
--   Goldreich and Ostrovsky, Software protection and simulation on oblivious RAMs, J. ACM 43 (1996), p. 470, §6, proof of THEOREM 6.1, final display (corrected); https://doi.org/10.1145/233551.233553

import Mathlib
import Definitions.Def_ObliviousRAM_LowerBound_Game

namespace ObliviousRAM.LowerBound

theorem counting_inequality {b m t : ℕ} (P : ObliviousPlayer b m t)
    (r : Fin t → Fin m) (a : List (Action m)) (ha : a ∈ (P.play r).support) :
    m ^ t ≤ (b + 2) ^ a.length * (Nat.multichoose a.length t * b ^ t) := by sorry

end ObliviousRAM.LowerBound
