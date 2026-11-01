-- Prove2me | Theorems.Thm_OpenSearchElectionTimer_randomDelay_range
-- name    : OpenSearchElectionTimer.randomDelay_range
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-11-01T01:02:52.551184+00:00
-- url     : https://prove2.me/theorems/2a57360b-b5f2-444c-a78d-efcdd42e5353
-- title:
--   Every random delay lies between one millisecond and the bound
-- statement:
--   For every natural number `M` with `1 ≤ M` and every draw `x : Fin (2^64)`: `1 ≤ randomDelay M x` and `randomDelay M x ≤ M`. The random part of an attempt's delay lies in `(0, M]`, the range stated by the scheduler's documentation (`ElectionSchedulerFactory.java:71-83, 163-167`).
-- source:
--   OpenSearch b2a54ba5c0defba3d1d20423e911d4bf920bab19: ElectionSchedulerFactory (documented delay distribution lines 71-83, settings 85-115, constructor 124-144, nonNegative 159-161, toPositiveLongAtMost 163-172, scheduleNextElection 195-241 with the bound at 203, the delay at 204 and the next attempt scheduled with the election duration as grace period at 218): https://github.com/opensearch-project/OpenSearch/blob/b2a54ba5c0defba3d1d20423e911d4bf920bab19/server/src/main/java/org/opensearch/cluster/coordination/ElectionSchedulerFactory.java#L62-L254; Coordinator (the scheduler built over the node's Random lines 262-263, the scheduler started after bootstrapping at 1158 and when a candidate has found a quorum of peers 1534-1550, startElectionScheduler 1567-1618 with grace period 0 at 1574, the same Random used to choose a node to abdicate to at 1818): https://github.com/opensearch-project/OpenSearch/blob/b2a54ba5c0defba3d1d20423e911d4bf920bab19/server/src/main/java/org/opensearch/cluster/coordination/Coordinator.java; DiscoveryModule (each node's Random created as new Random(Randomness.get().nextLong()), line 213): https://github.com/opensearch-project/OpenSearch/blob/b2a54ba5c0defba3d1d20423e911d4bf920bab19/server/src/main/java/org/opensearch/discovery/DiscoveryModule.java#L213; java.util.Random (a 48-bit linear congruential generator; nextLong): https://docs.oracle.com/en/java/javase/21/docs/api/java.base/java/util/Random.html; maxDelay, nonNegative and toPositiveLongAtMost as transcribed by the OpenSearchPreVote mission

import Definitions.Def_OpenSearchElectionTimer
open OpenSearchPreVote OpenSearchElectionTimer

theorem OpenSearchElectionTimer.randomDelay_range (M : Nat) (hM : 1 ≤ M) (x : Fin (2 ^ 64)) :
    1 ≤ randomDelay M x ∧ randomDelay M x ≤ M := by sorry
