-- Prove2me | Theorems.Thm_FreeReplExchange_Supplement_theorem_8
-- name    : FreeReplExchange.Supplement.theorem_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-17T02:38:54.064387+00:00
-- url     : https://prove2.me/theorems/a8e71b09-3405-4003-ada8-10df87a801c9
-- title:
--   Theorem 8 -- cyclic-exchange sharing maximization is NP-hard
-- statement:
--   Maximizing the final number of filled slots under the accepting strategy profile among MIC protocols using cyclic exchanges of single goods is NP-hard, even under ESC with exactly three goods and cycle length at most three.
--
--   Formally, the binary threshold language asking whether some such MIC schedule reaches at least $T$ filled slots is NP-hard under polynomial-time many-one reductions. In the reduction from 6-regular Tripartite Triangle Partition, the initial filled count is $5q$ and the threshold is $T=8q$; equality holds exactly when the graph has a triangle partition.
--
--   Differences from the source:
--   - encoding: hardness of maximizing filled slots → NP-hardness of the binary threshold decision language `cycleSharingLanguage`; reason: this is the standard decision formulation of the same exact optimization problem and retains ESC, exactly three goods, MIC, accept-all, no onward sharing, atomic whole-cycle acceptance, and cycle length at most three
--   - encoding: an exchange protocol observed under accept-all → a finite accepting-path schedule of MIC proposal lists; reason: off-path behavior does not change which accept-all terminal allocations and thresholds are attainable
-- source:
--   Yang--Kandasamy, Pairwise Exchanges of Freely Replicable Goods with Negative Externalities, arXiv:2603.12403 (held version, sha256 3ae07967...), Theorem 8, pp.28--29 (PDF pp.30--31)

import Mathlib
import Definitions.Def_FreeReplExchange_Supplement_CycleExchange

set_option autoImplicit false

namespace FreeReplExchange.Supplement

/-- Theorem 8, Yang--Kandasamy, *Pairwise Exchanges of Freely Replicable Goods with Negative
Externalities*, arXiv:2603.12403 (held version, sha256 3ae07967...), p. 28 (PDF p. 30): maximizing
the accepting-profile number of filled slots among MIC protocols using cyclic exchanges of single
goods is NP-hard, even under ESC with exactly three goods and cycles of length at most three.

**Formalization Note.** `cycleSharingLanguage` is the polynomially encoded threshold decision
version.  The reduction from 6-regular Tripartite Triangle Partition has initial filled count `5*q`
and reaches the threshold `8*q` exactly when the graph has a triangle partition. -/
theorem theorem_8 : KingTerrain.NPHard.IsNPHard cycleSharingLanguage := by sorry

end FreeReplExchange.Supplement
