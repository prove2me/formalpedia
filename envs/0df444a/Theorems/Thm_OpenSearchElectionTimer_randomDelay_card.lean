-- Prove2me | Theorems.Thm_OpenSearchElectionTimer_randomDelay_card
-- name    : OpenSearchElectionTimer.randomDelay_card
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-11-01T01:03:23.558862+00:00
-- url     : https://prove2.me/theorems/749592dc-16be-4a22-bd2d-90ac6df8a5a0
-- title:
--   The exact distribution of a random delay
-- statement:
--   For all natural numbers `M` and `d` with `1 ≤ M ≤ 2^63` and `1 ≤ d ≤ M`: the number of draws `x : Fin (2^64)` with `randomDelay M x = d` is exactly `2 · (⌊(2^63 − d) / M⌋ + 1)`.
--
--   Equivalently, writing `2^63 = qM + r` with `0 ≤ r < M`, each of the delays `1, …, r` has probability `(q + 1) / 2^63` and each of the delays `r + 1, …, M` has probability `q / 2^63`, for a draw uniform over the `2^64` longs: `nonNegative` maps the longs two-to-one onto `[0, 2^63)`, and the residues modulo `M` of `[0, 2^63)` occur `q + 1` or `q` times. The distribution is uniform exactly when `M` divides `2^63`.
-- source:
--   OpenSearch b2a54ba5c0defba3d1d20423e911d4bf920bab19: ElectionSchedulerFactory (documented delay distribution lines 71-83, settings 85-115, constructor 124-144, nonNegative 159-161, toPositiveLongAtMost 163-172, scheduleNextElection 195-241 with the bound at 203, the delay at 204 and the next attempt scheduled with the election duration as grace period at 218): https://github.com/opensearch-project/OpenSearch/blob/b2a54ba5c0defba3d1d20423e911d4bf920bab19/server/src/main/java/org/opensearch/cluster/coordination/ElectionSchedulerFactory.java#L62-L254; Coordinator (the scheduler built over the node's Random lines 262-263, the scheduler started after bootstrapping at 1158 and when a candidate has found a quorum of peers 1534-1550, startElectionScheduler 1567-1618 with grace period 0 at 1574, the same Random used to choose a node to abdicate to at 1818): https://github.com/opensearch-project/OpenSearch/blob/b2a54ba5c0defba3d1d20423e911d4bf920bab19/server/src/main/java/org/opensearch/cluster/coordination/Coordinator.java; DiscoveryModule (each node's Random created as new Random(Randomness.get().nextLong()), line 213): https://github.com/opensearch-project/OpenSearch/blob/b2a54ba5c0defba3d1d20423e911d4bf920bab19/server/src/main/java/org/opensearch/discovery/DiscoveryModule.java#L213; java.util.Random (a 48-bit linear congruential generator; nextLong): https://docs.oracle.com/en/java/javase/21/docs/api/java.base/java/util/Random.html; maxDelay, nonNegative and toPositiveLongAtMost as transcribed by the OpenSearchPreVote mission

import Definitions.Def_OpenSearchElectionTimer
open OpenSearchPreVote OpenSearchElectionTimer

theorem OpenSearchElectionTimer.randomDelay_card (M d : Nat) (hM : 1 ≤ M) (hM' : M ≤ 2 ^ 63)
    (hd : 1 ≤ d) (hdM : d ≤ M) :
    (Finset.univ.filter (fun x : Fin (2 ^ 64) => randomDelay M x = d)).card = 2 * ((2 ^ 63 - d) / M + 1) := by sorry
