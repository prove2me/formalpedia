-- Prove2me | Theorems.Thm_KServer_chunk_two_point_expTotal_le
-- name    : KServer.chunk_two_point_expTotal_le
-- status  : Proved
-- author  : @Gabewhigham
-- created : 2026-09-10T09:48:22.789841+00:00
-- url     : https://prove2.me/theorems/66614a2f-82de-4f31-af7b-368263ae1e3f
-- title:
--   Two-point rigidity: a chunk system on two points has expected total at most $c_B+jb$
-- statement:
--   Let $X$ be a metric space consisting of exactly two points $s\\neq t$, and let $C$ be a chunk system with online escapes on $X$ with marked points $s,t$, **size floor $0$** and size ceiling $c_B$ (a `ChunkSystemB X s t 0 cB T pe mL`). Assume the Doob martingale $D_h=\\mathbb E[\\sum_j c_j\\mid\\mathcal F_h]$ of its total mass has the pointwise jump bound $|D_{h+1}-D_h|\\le jb$.
--
--   **Statement.** The expected total size of $C$ is at most one chunk plus one Doob jump:
--   $$\\mathbb E\\Bigl[\\sum_j c_j\\Bigr]\\;\\le\\;c_B+jb .$$
--
--   **Why.** On two points the offline constraint `hopt` (an offline evader starting at $s$ pays at most $d(s,t)$ on the whole request sequence) makes the request sequence rigid: once a request avoids $s$, every later request must contain $t$, since otherwise the offline evader would be forced to cross between $s$ and $t$ twice, at cost $2d(s,t)$. Consequently a *lazy* evader — one that stays at $s$ while the requests allow it and stays at $t$ afterwards — pays nothing on any chunk in which the crossing neither happens nor may happen. The chunk-cost axiom then forces such a chunk to have size $0$. Hence a chunk carries mass only at times $h$ at which the crossing has positive conditional probability, and the first such time $\\sigma$ is a stopping time. Before $\\sigma$ no mass is consumed; on the branch of the atom of $\\sigma$ that crosses, the whole future mass collapses to $0$ in one step, so by the one-step Doob bound the conditional future mass at $\\sigma$ is at most $c_B+jb$. Optional stopping over the time-$0$ atoms turns this into the stated bound on the expected total.
--
--   **Relevance to the mission.** This is a rigidity (no-go) statement: it shows that the BCR chunk machinery cannot produce large mass on a two-point metric space, so a two-point space cannot witness a failure of the regrouping lemmas.

import Mathlib
import Definitions.Def_KServer_model
import Definitions.Def_KServer_evader
import Definitions.Def_KServer_evader_bail
import Definitions.Def_KServer_chunk_system_b
import Definitions.Def_KServer_chunk_cond

namespace KServer

theorem chunk_two_point_expTotal_le {X : Type*} [MetricSpace X] {s t : X}
    {cB T pe : ℝ} {mL : ℕ} (C : ChunkSystemB X s t 0 cB T pe mL)
    (hst : s ≠ t) (htwo : ∀ x : X, x = s ∨ x = t)
    {jb : ℝ} (hjb : C.DoobJumpBound jb) :
    ∑ ω, C.P ω * ∑ i, C.size ω i ≤ cB + jb := by sorry

end KServer
