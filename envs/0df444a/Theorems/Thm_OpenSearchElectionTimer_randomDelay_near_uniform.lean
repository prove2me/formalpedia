-- Prove2me | Theorems.Thm_OpenSearchElectionTimer_randomDelay_near_uniform
-- name    : OpenSearchElectionTimer.randomDelay_near_uniform
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-11-01T01:03:49.206662+00:00
-- url     : https://prove2.me/theorems/7bb0fbcd-6639-482e-bb8f-00e2d50c7f13
-- title:
--   Random delays are uniform up to a relative error of M / 2^63
-- statement:
--   For all natural numbers `M` and `d` with `1 ≤ M ≤ 2^63` and `1 ≤ d ≤ M`: `2 · ⌊2^63 / M⌋ ≤ #{x : Fin (2^64) | randomDelay M x = d} ≤ 2 · ⌈2^63 / M⌉`, the ceiling being written `(2^63 + M − 1) / M`.
--
--   For a uniform draw, each delay `d ∈ [1, M]` has a probability between `⌊2^63 / M⌋ / 2^63` and `⌈2^63 / M⌉ / 2^63`, that is, within a factor `1 ± M / 2^63` of `1 / M`. For the default maximum timeout `M = 10000` milliseconds, `M / 2^63` is about `1.1 · 10^-15`.
-- source:
--   OpenSearch b2a54ba5c0defba3d1d20423e911d4bf920bab19: ElectionSchedulerFactory (documented delay distribution lines 71-83, settings 85-115, constructor 124-144, nonNegative 159-161, toPositiveLongAtMost 163-172, scheduleNextElection 195-241 with the bound at 203, the delay at 204 and the next attempt scheduled with the election duration as grace period at 218): https://github.com/opensearch-project/OpenSearch/blob/b2a54ba5c0defba3d1d20423e911d4bf920bab19/server/src/main/java/org/opensearch/cluster/coordination/ElectionSchedulerFactory.java#L62-L254; Coordinator (the scheduler built over the node's Random lines 262-263, the scheduler started after bootstrapping at 1158 and when a candidate has found a quorum of peers 1534-1550, startElectionScheduler 1567-1618 with grace period 0 at 1574, the same Random used to choose a node to abdicate to at 1818): https://github.com/opensearch-project/OpenSearch/blob/b2a54ba5c0defba3d1d20423e911d4bf920bab19/server/src/main/java/org/opensearch/cluster/coordination/Coordinator.java; DiscoveryModule (each node's Random created as new Random(Randomness.get().nextLong()), line 213): https://github.com/opensearch-project/OpenSearch/blob/b2a54ba5c0defba3d1d20423e911d4bf920bab19/server/src/main/java/org/opensearch/discovery/DiscoveryModule.java#L213; java.util.Random (a 48-bit linear congruential generator; nextLong): https://docs.oracle.com/en/java/javase/21/docs/api/java.base/java/util/Random.html; maxDelay, nonNegative and toPositiveLongAtMost as transcribed by the OpenSearchPreVote mission

import Definitions.Def_OpenSearchElectionTimer
open OpenSearchPreVote OpenSearchElectionTimer

theorem OpenSearchElectionTimer.randomDelay_near_uniform (M d : Nat) (hM : 1 ≤ M) (hM' : M ≤ 2 ^ 63)
    (hd : 1 ≤ d) (hdM : d ≤ M) :
    2 * (2 ^ 63 / M) ≤ (Finset.univ.filter (fun x : Fin (2 ^ 64) => randomDelay M x = d)).card ∧
    (Finset.univ.filter (fun x : Fin (2 ^ 64) => randomDelay M x = d)).card ≤ 2 * ((2 ^ 63 + M - 1) / M) := by sorry
