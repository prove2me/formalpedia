-- Prove2me | Theorems.Thm_MultipleUnicast_Counterexample_terminal_distance
-- name    : MultipleUnicast.Counterexample.terminal_distance
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-08T10:22:49.012451+00:00
-- url     : https://prove2.me/theorems/758615f2-3dd9-443b-96f8-080438f14a7a
-- title:
--   Section 4, unnumbered terminal distance — every session connected and at least five
-- statement:
--   For each of the source's sessions $q\in B$, its endpoints $s_q,t_q$ are connected in the physical graph $G$ and
--   $$\operatorname{dist}_G(s_q,t_q)\ge5.$$
--   The endpoints are the earlier and later vertices in the given order, without a fixed point-to-line source convention. This expresses the terminal separation used for fractional routing while making the finite-distance convention explicit.
--
--   Differences from the source:
--   - encoding: the source labels vertices and candidate edges by integers and sessions by B → Fin 182 and Fin 910 labels, with a fixed equivalence B ≃ Fin (card B) where needed; reason: the same finite objects and source/sink order are retained
--   - encoding: the terminal distance is at least five → reachability together with the natural-valued graph-distance bound; reason: reachability makes the source distance finite and excludes the disconnected zero default
-- source:
--   Mark Braverman, Zhongtian He, STOC 2027 submission #286 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/286.pdf, §4, unnumbered dist_G(s_q,t_q) ≥ 5 display, PDF p. 12 / printed p. 11

import Definitions.Def_MultipleUnicast_Counterexample_Protocol

set_option maxRecDepth 2048

namespace MultipleUnicast.Counterexample

/-- §4 terminal-distance display. Reachability excludes the disconnected-distance default. -/
theorem terminal_distance : ∀ i : Fin network.k,
    graph.Reachable (network.s i) (network.t i) ∧
    5 ≤ graph.dist (network.s i) (network.t i) := by sorry

end MultipleUnicast.Counterexample
