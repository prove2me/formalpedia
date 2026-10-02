-- Prove2me | Theorems.Thm_KServer_chunk_zero_floor
-- name    : KServer.chunk_zero_floor
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-02T09:18:09.92424+00:00
-- url     : https://prove2.me/theorems/7bd7a45e-d2d2-411a-90d0-155cbf6965c2
-- title:
--   The size floor of a chunk system can be lowered to zero at no cost
-- statement:
--   **The size floor of a chunk system is free to lower.** Write a chunk system from $s$ to $t$ with size floor $c_{\mathrm{Lo}}$, ceiling $c_{\mathrm{Hi}}$, expected total at least $T$, escape price $p$ and at least $m_{\mathrm{Lo}}$ chunks. If $c_{\mathrm{Lo}} \ge 0$, then there exists a chunk system on the *same* space at floor $0$ with the *same* number of chunks and the *same* sizes: same outcomes, weights, chunk count, filtration, chunks, sizes, expected total bound, escape price and chunk-count bound.\n\nThe floor `cLo` occurs in exactly one field of `ChunkSystemB`, namely the lower half of the size bound $$c_{\mathrm{Lo}} \le c_j \le c_{\mathrm{Hi}},$$\nand there only as a lower bound. Every other field -- the positivity and normalisation of the weights, the chunk-count bounds, refinement, adaptedness, measurability of the sizes, nonemptiness of the requests, the terminal-request and offline-optimality conditions, the conditional cost bound and the expected-total bound -- is literally the same proposition at floor $0$ as at floor $c_{\mathrm{Lo}}$. So the structure is rebuilt field by field, copying all of them and weakening only the lower half of the size bound.\n\n**Why this matters.** In the BCR level induction, `BCRInductiveChunks` at level $w$ carries floor $3^w/2$, while `BCRInductiveSubchunks` at level $w+1$ carries floor $0$. Every Proved level-step constructor -- `level_step_full`, `level_step_sturdy`, `chunk_regrid`, `chunk_combining`, and the mass-normalisation and sturdiness lemmas `chunk_scale_total` and `chunk_restrict_sturdy` -- is *stated* at floor $0$, and each takes its input chunk system at floor $0$. They are therefore inapplicable to a level-$w$ system, whose floor is positive for every $w \ge 0$. This lemma supplies exactly the missing link, and it is the cheapest possible one: no new mathematics, only the observation that the floor is a one-sided parameter.

import Mathlib
import Definitions.Def_KServer_evader
import Definitions.Def_KServer_evader_bail
import Definitions.Def_KServer_chunk_system_b

namespace KServer

/-- The size floor of a chunk system is a one-sided parameter, so it can be
lowered to zero at no cost: the same chunk data, on the same space, is a valid
chunk system at floor `0`, with the same number of chunks. -/
theorem chunk_zero_floor {X : Type*} [MetricSpace X] {s t : X}
    {cA cHi total price : ℝ} {mLo : ℕ}
    (C : ChunkSystemB X s t cA cHi total price mLo) (hA : 0 ≤ cA) :
    ∃ C' : ChunkSystemB X s t 0 cHi total price mLo, C'.m = C.m := by sorry

end KServer
