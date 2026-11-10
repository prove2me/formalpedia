-- Prove2me | Theorems.Thm_GoldsteinMCSP_Hardness_lemma_1_1
-- name    : GoldsteinMCSP.Hardness.lemma_1_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T17:12:54.97069+00:00
-- url     : https://prove2.me/theorems/627f0212-2140-4ba6-a383-d743a0ac9527
-- title:
--   Lemma 1.1 — exact conflict-graph characterization
-- statement:
--   Let A and B be related finite unsigned strings, and let n be their common length. Construct their conflict graph on occurrence-specific matching adjacent letter pairs, with conflicts as in Section 1.1. Write m for the attained minimum number of common blocks and α for the attained maximum independent-set cardinality. Then
--
--   $$m+α=n.$$
--
--   The result includes empty strings, for which all three quantities are zero. Repeated letters and repeated blocks retain their multiplicities; there is no two-copy restriction in this lemma.
--
--   Differences from the source:
--   - encoding: finite strings over a letter alphabet → finite lists of natural-number labels; reason: every finite input can be relabelled without changing multiplicities or contiguous blocks
--   - encoding: partitions into contiguous blocks → cut partitions with nonempty blocks, and the empty partition of an empty word; reason: empty blocks may be deleted without changing the optimum; this makes the standard cut-partition convention explicit
--   - encoding: n − MIS(G) = m → m + MIS(G) = n; reason: this equivalent natural-number equality avoids truncated subtraction; independent matches use distinct duos, so MIS(G) ≤ n
-- source:
--   Goldstein, Kolman and Zheng (2005), Minimum Common String Partition Problem: Hardness and Approximations, EJC 12, R50, DOI 10.37236/1947, Lemma 1.1, printed p. 5 (PDF p. 5)

import Definitions.Def_GoldsteinMCSP_Hardness_Conflict

namespace GoldsteinMCSP.Hardness

theorem lemma_1_1 (a b : Word) (h : related a b) :
    optimum a b + conflictMIS [a] [b] = a.length := by sorry

end GoldsteinMCSP.Hardness
