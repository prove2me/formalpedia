-- Prove2me | Theorems.Thm_OpenSearchLivenessTimed_delta_star_sufficient
-- name    : OpenSearchLivenessTimed.delta_star_sufficient
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-11-01T18:51:40.51361+00:00
-- url     : https://prove2.me/theorems/fbaf1583-a28a-4534-b2b7-80d59ad7aa2c
-- title:
--   The margin δ* = 4D + P suffices for a win to precede any competitor
-- statement:
--   If the first candidate wins by time $t_0 + 4D + P$ (one message hop each for the pre-vote request, the pre-vote response, the start-join, and the join back, plus total local processing $P$), and every competitor fires at or after $t_0 + \delta$ with $\delta > 4D + P$, then the win strictly precedes any competitor's firing time, hence precedes any start-join handling by a competitor.
-- source:
--   OpenSearch cluster coordination, pinned revision b2a54ba5c0defba3d1d20423e911d4bf920bab19 (org.opensearch.cluster.coordination); liveness/timer gap-closure analysis, new theorems mechanized from the branch's OpenSearchCoordination/OpenSearchPreVote/OpenSearchSafety/OpenSearchProgress missions.

import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Order.Basic
import Mathlib.Order.Filter.AtTopBot.Basic

theorem OpenSearchLivenessTimed.delta_star_sufficient (t0 D P δ win competitor : Int)
    (hwin : win ≤ t0 + 4 * D + P) (hcomp : t0 + δ ≤ competitor)
    (hδ : 4 * D + P < δ) : win < competitor := by sorry
