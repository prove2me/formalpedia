-- Prove2me | Theorems.Thm_GraphSimOT_Gaps_theorem_14
-- name    : GraphSimOT.Gaps.theorem_14
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T18:06:48.193341+00:00
-- url     : https://prove2.me/theorems/789ec02d-7aef-4e24-81d8-c42b51fd30b7
-- title:
--   Theorem 14 — δ_2 ≤ δ^OT_2 + 2√(2δ^OT_2)
-- statement:
--   For all graphs $G, H$ of the same order,
--   $$\delta_2(G,H)\ \le\ \delta^{OT}_2(G,H) + 2\sqrt{2\,\delta^{OT}_2(G,H)},$$
--   where $\delta_2 = d_2/n$ is the normalised spectral distance (operator $2\to2$ norm) and $\delta^{OT}_2 = \min_{Q^*\in\mathrm{DS}^*}\|B_{2\to2}(G,H,Q^*)\|_{2\to2}$.
--
--   As $\delta^{OT}_2\le1$ this gives clause (iv) of Theorem 2, $\delta_2\le(1+2\sqrt2)\sqrt{\delta^{OT}_2}$.
--
--   Differences from the source:
--   - encoding: graphs G, H of the same order n with vertex sets V, W → G H : SimpleGraph (Fin n); reason: every pair of graphs of order n is isomorphic to a pair on Fin n and all distances are isomorphism-invariant; the paper itself takes V(G) = V(H) = [n] in App. E.2 and F.2
--   - encoding: δ^OT_2 defined as a minimum → sInf of the costs over the fractional alignments (bijective distances: Finset.inf' over all permutations, a genuine minimum); reason: the set of costs is nonempty and bounded below by 0, and the paper shows the minimum is attained (pp. 14–15), so the infimum is the minimum
-- source:
--   Breitung, Gervens, Grohe, Graph Similarity Meets Optimal Transport, arXiv:2611.05048 (held version, sha256 1cd10e91…), p. 12, Theorem 14

import Mathlib
import Definitions.Def_GraphSimOT_Gaps_Distances

namespace GraphSimOT.Gaps

/-- Theorem 14 (p. 12): for all graphs `G, H` of the same order,
`δ_2(G, H) ≤ δ^OT_2(G, H) + 2 √(2 δ^OT_2(G, H))`. -/
theorem theorem_14 {n : ℕ} (G H : SimpleGraph (Fin n)) :
    delta2 G H ≤ deltaOT2 G H + 2 * Real.sqrt (2 * deltaOT2 G H) := by sorry

end GraphSimOT.Gaps
