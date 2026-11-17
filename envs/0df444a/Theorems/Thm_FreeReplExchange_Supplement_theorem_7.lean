-- Prove2me | Theorems.Thm_FreeReplExchange_Supplement_theorem_7
-- name    : FreeReplExchange.Supplement.theorem_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-17T02:38:23.973906+00:00
-- url     : https://prove2.me/theorems/ebcd309e-e289-4fd5-8204-113631737535
-- title:
--   Theorem 7 -- bundle-exchange sharing maximization is NP-hard
-- statement:
--   Maximizing the final number of filled slots under the accepting strategy profile among MIC protocols using pairwise exchanges of nonempty bundles is NP-hard, even under ESC and when every bundle has at most five goods.
--
--   Formally, the binary threshold language asking whether some such MIC schedule reaches at least $T$ filled slots is NP-hard under polynomial-time many-one reductions. The X3C reduction uses
--
--   $$
--   T=5+3|\mathcal C|+K+8q,\qquad K=2\nu,
--   $$
--
--   where $\nu$ is the maximum matching cardinality of the polynomially computable set-agent slot graph.
--
--   Differences from the source:
--   - encoding: hardness of maximizing filled slots → NP-hardness of the binary threshold decision language `bundleSharingLanguage`; reason: this is the standard decision formulation of the same exact optimization problem and retains the source's ESC, MIC, accept-all, no-onward-sharing, atomicity, and bundle-size-five restrictions
--   - encoding: an exchange protocol observed under accept-all → a finite accepting-path schedule of MIC proposal sets; reason: off-path behavior does not change which accept-all terminal allocations and thresholds are attainable
-- source:
--   Yang--Kandasamy, Pairwise Exchanges of Freely Replicable Goods with Negative Externalities, arXiv:2603.12403 (held version, sha256 3ae07967...), Theorem 7, pp.26--28 (PDF pp.28--30), eq. (14)

import Mathlib
import Definitions.Def_FreeReplExchange_Supplement_BundleExchange

set_option autoImplicit false

namespace FreeReplExchange.Supplement

/-- Theorem 7, Yang--Kandasamy, *Pairwise Exchanges of Freely Replicable Goods with Negative
Externalities*, arXiv:2603.12403 (held version, sha256 3ae07967...), p. 26 (PDF p. 28): maximizing
the accepting-profile number of filled slots among MIC protocols using pairwise exchanges of
bundles is NP-hard, even under ESC and when every bundle has at most five goods.

**Formalization Note.** `bundleSharingLanguage` is the polynomially encoded threshold decision
version of the maximization problem.  The source reduction from X3C uses threshold
`5 + 3*|C| + K + 8*q`, where `K = 2*nu` and `nu` is the maximum cardinality of the set-agent slot
graph; this exact threshold is part of the proof obligation for the NP-hardness assertion. -/
theorem theorem_7 : KingTerrain.NPHard.IsNPHard bundleSharingLanguage := by sorry

end FreeReplExchange.Supplement
