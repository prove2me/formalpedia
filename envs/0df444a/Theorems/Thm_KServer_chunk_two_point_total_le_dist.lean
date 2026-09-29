-- Prove2me | Theorems.Thm_KServer_chunk_two_point_total_le_dist
-- name    : KServer.chunk_two_point_total_le_dist
-- status  : Proved
-- author  : @Gabewhigham
-- created : 2026-09-10T10:17:32.807694+00:00
-- url     : https://prove2.me/theorems/e69d4c3b-d0f6-4b34-910e-298395f1ed35
-- title:
--   On two points every chunk system has total at most $d(s,t)$
-- statement:
--   Suppose the metric space $X$ consists of exactly two points $s\\neq t$. Then every chunk system with online escapes on $X$ with marked points $s,t$ and declared total $T$ satisfies
--   $$T\\;\\le\\;d(s,t).$$
--
--   **Why.** The offline constraint built into a chunk system says that an offline evader starting at $s$ serves the whole request sequence for at most $d(s,t)$. On two points this forces the sequence to be rigid: once a request avoids $s$, every later request contains $t$, for otherwise the offline evader would have to cross twice. Therefore the *one-way lazy* evader — which stays at $s$ while every request so far contains $s$ and moves to $t$ for good afterwards — is a legitimate online evader that pays at most one crossing, i.e. at most $d(s,t)$, on every such sequence. Since the expected total size of a chunk system is bounded by the expected cost of any evader, and the declared total is a lower bound for the expected total size, the claim follows.
--
--   **Consequence.** No chunk system on a two-point space can carry more mass than a single crossing. In particular the inductive chunk statements of the Bubeck–Coester–Rabani programme are unsatisfiable over two-point spaces whenever the total they demand exceeds $d(s,t)$, so no two-point instance can witness a failure of the regrouping lemmas. No hypothesis on the size floor, the size ceiling or the martingale of the total is needed.

import Mathlib
import Definitions.Def_KServer_model
import Definitions.Def_KServer_evader
import Definitions.Def_KServer_evader_bail
import Definitions.Def_KServer_chunk_system_b
import Definitions.Def_KServer_chunk_cond
import Definitions.Def_KServer_chunk_saturate

namespace KServer

theorem chunk_two_point_total_le_dist {X : Type*} [MetricSpace X] {s t : X}
    {cLo cHi total price : ℝ} {mL : ℕ} (C : ChunkSystemB X s t cLo cHi total price mL)
    (hst : s ≠ t) (htwo : ∀ x : X, x = s ∨ x = t) : total ≤ dist s t := by sorry

end KServer
