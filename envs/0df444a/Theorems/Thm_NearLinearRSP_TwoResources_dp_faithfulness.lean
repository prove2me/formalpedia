-- Prove2me | Theorems.Thm_NearLinearRSP_TwoResources_dp_faithfulness
-- name    : NearLinearRSP.TwoResources.dp_faithfulness
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:25:54.016926+00:00
-- url     : https://prove2.me/theorems/a3e4f11f-c169-43c8-ae4b-d52809577a62
-- title:
--   Observation A.1 — DP Bellman inequality and selected-edge equality
-- statement:
--   Fix an inner input with source $s$, thresholds $L,C>0$ and accuracy $0<\delta<1$, and let DP be the table actually built by the queue algorithm. For every directed edge $uv$ and every pair of nonnegative tick indices $i,j$, let $L_{uv}$ and $C_{uv}$ be independent Poisson increments with the specified length and cost rates. Then
--   $$
--   \mathrm{DP}(v,i,j)\le\mathbb E[\mathrm{DP}(u,i+L_{uv},j+C_{uv})].
--   $$
--   If $i,j<q$ and the recorded parent is the edge predecessor $u$, equality holds. A virtual tick is a separate labelled parent, not an edge crossing.
--
--   This is the faithfulness property used to relate the queue computation to adaptive escape plans. The expectation is represented by the exact finite rectangle and overflow mass; both indices saturate to value one at or above $q$, even at the source.
--
--   Differences from the source:
--   - encoding: inner accuracy epsilon and q = Theta(epsilon^-2) → accuracy delta in (0,1), q = ceil(512/delta^2), acceptance 1/4; reason: consistent renaming and an explicit sufficiently large constant, preserving both approximation factors
--   - encoding: the Section 4 DP table on a finite directed graph → the fixed queue computation on incident vertices and the source, with value-one defaults, stable ties and self-loops skipped; reason: isolated vertices cannot be accepted and removing nonnegative self-loops preserves every feasible optimum; no Bellman or correctness property is assumed
--   - encoding: expectation and all table state indices → finite-rectangle expectation with exact overflow and saturated value-one extension for every natural index; equality for edge parents; reason: the expectation depends only on this finite marginal; virtual ticks are not edges and saturated states have expectation one
-- source:
--   Vikrant Ashvinkumar, STOC 2027 submission #289 (October 2026), p.14, Observation A.1

import Definitions.Def_NearLinearRSP_TwoResources_RAM

set_option autoImplicit false

namespace NearLinearRSP.TwoResources

theorem dp_faithfulness (A : InnerInput) :
    ∀ u v : ℕ, (u, v) ∈ A.I.graph.edges → ∀ i j : ℕ,
      dpValue A (buildTable A) v i j ≤ edgeExpectation A (buildTable A) u v i j ∧
      (i < tickLimit A → j < tickLimit A →
        (buildTable A v i j).parent = .edge u →
        dpValue A (buildTable A) v i j = edgeExpectation A (buildTable A) u v i j) := by sorry

end NearLinearRSP.TwoResources
