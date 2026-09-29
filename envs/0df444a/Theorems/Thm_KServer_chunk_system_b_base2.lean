-- Prove2me | Theorems.Thm_KServer_chunk_system_b_base2
-- name    : KServer.chunk_system_b_base2
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-01T20:31:40.423756+00:00
-- url     : https://prove2.me/theorems/c1529e7e-2aed-4e45-98db-0c85bc5af591
-- title:
--   Path-space base chunk system with a free escape price
-- statement:
--   The base case of the BCR chunk induction, with the escape price as a free parameter. On the path metric on $\{0, 1, \dots, \beta\}$ (consecutive points at distance $1$), the marked endpoints are at distance $\beta$, and for any $\alpha \ge 0$ and level $w$ with $\alpha w^2 \le 1$, and any escape price $p \ge 1$, there is a chunk system between the endpoints with deterministic outcomes, sizes in $[\tfrac12, \tfrac32]$, at least $\lceil \alpha\beta w^2 \rceil$ chunks, expected total at least $\alpha w^2 \beta$, and per-chunk conditional cost claims financed by the escape price $p$. The cruel single-file request pattern forces cost $1$ per chunk however the evader plays, and bailing at any prefix costs the full price $p \ge 1$, so any price of at least one unit is sound. Freeing the price from the previously fixed value $2\beta$ lets the level recursion carry a price on the chunk-size scale, as required by the coin-phase separation arithmetic of the race construction.
-- source:
--   BCR randomized k-server lower bound

import Mathlib
import Definitions.Def_KServer_evader
import Definitions.Def_KServer_chunk_system
import Definitions.Def_KServer_chunk_system_f
import Definitions.Def_KServer_evader_bail
import Definitions.Def_KServer_chunk_system_b

namespace KServer

theorem chunk_system_b_base2 (β : ℕ) (hβ : 1 ≤ β) (α : ℝ) (hα0 : 0 ≤ α) (w : ℕ)
    (hw : α * (w : ℝ) ^ 2 ≤ 1) (p : ℝ) (hp : 1 ≤ p) :
    letI := pathMetric β
    dist (0 : Fin (β + 1)) (Fin.last β) = β ∧
    Nonempty (ChunkSystemB (Fin (β + 1)) 0 (Fin.last β)
      (1 / 2) (3 / 2) (α * (w : ℝ) ^ 2 * β) p ⌈α * β * (w : ℝ) ^ 2⌉₊) := by sorry

end KServer
