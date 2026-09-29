-- Prove2me | Theorems.Thm_KServer_chunk_expTotal_le_evader_cost
-- name    : KServer.chunk_expTotal_le_evader_cost
-- status  : Proved
-- author  : @Gabewhigham
-- created : 2026-09-10T10:17:27.435763+00:00
-- url     : https://prove2.me/theorems/716c3da2-148b-4a5b-991a-750557c3bcb7
-- title:
--   The expected total size of a chunk system is at most the expected cost of any evader
-- statement:
--   Let $C$ be a chunk system with online escapes on a metric space $X$ with marked points $s,t$: a random sequence of $m$ chunks of set requests with adapted sizes $c_j$, a filtration, and the conditional cost bound against every evader and every online escape rule. Let $E$ be any evader algorithm on $X$ and let $\\sigma(\\omega)$ denote the flattened request sequence of the outcome $\\omega$.
--
--   **Statement.** The expected total size of $C$ never exceeds the expected cost that $E$ pays on the request sequence of $C$:
--   $$\\mathbb E\\Bigl[\\sum_j c_j\\Bigr]\\;\\le\\;\\mathbb E\\bigl[\\mathrm{cost}_E(\\sigma)\\bigr].$$
--
--   **Role.** The defining cost axiom of a chunk system bounds the size of each chunk, conditionally on the past, by the cost that an arbitrary evader pays on that chunk. Summing the axiom over the atoms of the time-$j$ filtration and then over the chunks — the per-chunk costs telescope to the cost on the whole sequence — turns those local bounds into one global inequality. It is the converse direction of the chunk machinery: whatever total mass a chunk system carries is genuinely paid by every evader, so a chunk system can never certify more mass than the true evasion cost of the underlying space. In particular it gives a uniform ceiling for the total of any chunk system built over a space on which some evader is cheap.

import Mathlib
import Definitions.Def_KServer_model
import Definitions.Def_KServer_evader
import Definitions.Def_KServer_evader_bail
import Definitions.Def_KServer_chunk_system_b
import Definitions.Def_KServer_chunk_cond
import Definitions.Def_KServer_chunk_saturate

namespace KServer

theorem chunk_expTotal_le_evader_cost {X : Type*} [MetricSpace X] {s t : X}
    {cLo cHi total price : ℝ} {mL : ℕ} (C : ChunkSystemB X s t cLo cHi total price mL)
    (E : EvaderAlgorithm X) :
    ∑ ω, C.P ω * ∑ i, C.size ω i ≤ ∑ ω, C.P ω * E.cost (C.seq ω) := by sorry

end KServer
