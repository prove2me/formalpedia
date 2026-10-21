-- Prove2me | Theorems.Thm_NetInspect_Rate_lemma_EC_2
-- name    : NetInspect.Rate.lemma_EC_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:03:13.41154+00:00
-- url     : https://prove2.me/theorems/e1bee5b3-060b-4370-8941-38c43d0da002
-- title:
--   Lemma EC.2, p. ec2 — m* ≤ n*
-- statement:
--   In every detection model (finite nodes and components, every component monitored from some node), the size $m^*$ of a maximum set packing is at most the size $n^*$ of a minimum set cover:
--   $$
--   m^*\le n^*.
--   $$
--
--   This weak-duality inequality between the two combinatorial problems (6) and (7) places the paper's case of interest $b_1<n^*$, $b_2<m^*$ in context and is used in the bounds of Proposition 1.
-- source:
--   Dahan, Sela & Amin, Network Inspection for Detecting Strategic Attacks, arXiv:1705.00349v4, p. ec2, Lemma EC.2

import Mathlib
import Definitions.Def_BlottoLP_Flow_ZeroSum
import Definitions.Def_NetInspect_Rate_Model

namespace NetInspect.Rate

open Finset DetectionModel

/-- Lemma EC.2 (p. ec2): the size of maximum set packings is at most the size of minimum set
covers, `m* ≤ n*`. -/
theorem lemma_EC_2 {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : DetectionModel V E) :
    G.mStar ≤ G.nStar := by sorry

end NetInspect.Rate
