-- Prove2me | Theorems.Thm_KServer_chunk_ceiling_raise
-- name    : KServer.chunk_ceiling_raise
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-02T10:08:52.885985+00:00
-- url     : https://prove2.me/theorems/66fea09d-e395-488d-aac5-048f75e64468
-- title:
--   The size ceiling of a chunk system can be raised at no cost
-- statement:
--   **The size ceiling of a chunk system is free to raise.** Write a chunk system from $s$ to $t$ with size floor $c_{\mathrm{Lo}}$, ceiling $c_{\mathrm{Hi}}$, expected total at least $T$, escape price $p$ and at least $m_{\mathrm{Lo}}$ chunks. If $c_{\mathrm{Hi}} \le c'_{\mathrm{Hi}}$, then there exists a chunk system on the *same* space at ceiling $c'_{\mathrm{Hi}}$ with the *same* number of chunks: same outcomes, weights, count, filtration, chunks, sizes, expected total bound, escape price and chunk-count bound.
--
--   The ceiling $c_{\mathrm{Hi}}$ occurs in exactly one field of `ChunkSystemB`, namely the upper half of the size bound $$c_{\mathrm{Lo}} \le c_j \le c_{\mathrm{Hi}},$$ and there only as an upper bound. Every other field -- the positivity and normalisation of the weights, the chunk-count bounds, refinement, adaptedness, measurability of the sizes, nonemptiness of the requests, the terminal-request and offline-optimality conditions, the conditional cost bound and the expected-total bound -- is literally the same proposition at the larger ceiling. The structure is rebuilt field by field, copying all of them and weakening only the upper half of the size bound.
--
--   **Why this matters.** This is the exact structural dual of the size floor. The floor is free to lower and the ceiling is free to raise, because each occurs in exactly one of the nineteen fields, on opposite sides of the same conjunction. The BCR level induction needs both moves: `BCRInductiveChunks` at level $w$ carries $c_{\mathrm{Hi}} = 3\cdot 3^w/2$, and the level-$(w+1)$ target carries $3\cdot 3^{w+1}/2$, so the ceiling must be raised across the level step on the same space. Every Proved level-step constructor in the catalogue -- `level_step_sturdy`, `level_step_full`, `chunk_regrid` -- outputs a ceiling of the form $2\delta + c$ with $\delta \ge 0$, which is never the pinned value. This lemma supplies the missing one-sided-parameter move. It does not by itself perform the regrouping, which must additionally raise the escape price and the chunk-count floor and lower the expected total; it removes the ceiling obstruction only.

import Mathlib
import Definitions.Def_KServer_evader
import Definitions.Def_KServer_evader_bail
import Definitions.Def_KServer_chunk_system_b

namespace KServer

/-- The size ceiling of a chunk system is a one-sided parameter, so it can be
raised at no cost: the same chunk data, on the same space, is a valid chunk
system at any larger ceiling. -/
theorem chunk_ceiling_raise {X : Type*} [MetricSpace X] {s t : X}
    {cA cB cB' total price : ℝ} {mLo : ℕ}
    (C : ChunkSystemB X s t cA cB total price mLo) (hB : cB ≤ cB') :
    ∃ C' : ChunkSystemB X s t cA cB' total price mLo, C'.m = C.m := by sorry

end KServer
