-- Prove2me | Theorems.Thm_OpenSearchLivenessTimed_epsilon_horizon
-- name    : OpenSearchLivenessTimed.epsilon_horizon
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-11-01T18:51:40.567954+00:00
-- url     : https://prove2.me/theorems/0d710605-fab9-4a61-a6d5-c125e77e5785
-- title:
--   Finite ε-horizon from a geometric all-contested bound
-- statement:
--   Given any sequence $\mathrm{allContested}$ of all-contested-round probabilities bounded geometrically, $\mathrm{allContested}\, K \leq b^K$ with $0 \leq b < 1$, for every $\varepsilon > 0$ there is a round count $K$ with $\mathrm{allContested}\, K < \varepsilon$. This is the finite form of probabilistic liveness: it turns a geometric bound into an explicit $\varepsilon$-horizon without claiming a deterministic bound, and it does not itself prove the geometric bound.
-- source:
--   OpenSearch cluster coordination, pinned revision b2a54ba5c0defba3d1d20423e911d4bf920bab19 (org.opensearch.cluster.coordination); liveness/timer gap-closure analysis, new theorems mechanized from the branch's OpenSearchCoordination/OpenSearchPreVote/OpenSearchSafety/OpenSearchProgress missions.

import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Order.Basic
import Mathlib.Order.Filter.AtTopBot.Basic

theorem OpenSearchLivenessTimed.epsilon_horizon (b : ℚ) (hb0 : 0 ≤ b) (hb1 : b < 1)
    (allContested : ℕ → ℚ) (hbound : ∀ K, allContested K ≤ b ^ K)
    (ε : ℚ) (hε : 0 < ε) : ∃ K, allContested K < ε := by sorry
