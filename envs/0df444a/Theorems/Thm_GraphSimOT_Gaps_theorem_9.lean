-- Prove2me | Theorems.Thm_GraphSimOT_Gaps_theorem_9
-- name    : GraphSimOT.Gaps.theorem_9
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T18:06:40.138359+00:00
-- url     : https://prove2.me/theorems/b87fbf72-7cba-4b37-891f-e8634428e284
-- title:
--   Theorem 9 — δ_1 ≤ 15√(δ^OT_1 ln(4/δ^OT_1))
-- statement:
--   For all graphs $G, H$ of the same order,
--   $$\delta_1(G,H)\ \le\ 15\sqrt{\delta^{OT}_1(G,H)\cdot\ln\big(4/\delta^{OT}_1(G,H)\big)},$$
--   where the right-hand side is defined as $0$ if $\delta^{OT}_1(G,H) = 0$. Here $\delta_1 = d_1/n$ is the normalised local edit distance (operator 1-norm) and $\delta^{OT}_1 = \min_{Q^*\in\mathrm{DS}^*}\|B_{1\to1}(G,H,Q^*)\|_{1\to1}$, with the convention $0^0 = 0$ in $B_{1\to1}$.
--
--   Proposition 8 shows that no linear bound $\delta_1\le c\,\delta^{OT}_1$ holds; Theorem 9 is the uniform non-linear bound, clause (ii) of Theorem 2.
--
--   **Formalization Note.** At $\delta^{OT}_1 = 0$ Lean evaluates $\ln(4/0) = \ln 0 = 0$, so the right-hand side is $15\sqrt{0} = 0$, the paper's convention.
--
--   Differences from the source:
--   - encoding: graphs G, H of the same order n with vertex sets V, W → G H : SimpleGraph (Fin n); reason: every pair of graphs of order n is isomorphic to a pair on Fin n and all distances are isomorphism-invariant; the paper itself takes V(G) = V(H) = [n] in App. E.2 and F.2
--   - encoding: δ^OT_1 defined as a minimum → sInf of the costs over the fractional alignments (bijective distances: Finset.inf' over all permutations, a genuine minimum); reason: the set of costs is nonempty and bounded below by 0, and the paper shows the minimum is attained (pp. 14–15), so the infimum is the minimum
--   - encoding: the right-hand side is defined as 0 if δ^OT_1(G, H) = 0 → 15 * √(δOT₁ * Real.log (4 / δOT₁)), which Lean evaluates to 0 at δOT₁ = 0; reason: same value: Real.log (4 / 0) = Real.log 0 = 0 and √0 = 0
-- source:
--   Breitung, Gervens, Grohe, Graph Similarity Meets Optimal Transport, arXiv:2611.05048 (held version, sha256 1cd10e91…), p. 9, Theorem 9

import Mathlib
import Definitions.Def_GraphSimOT_Gaps_Distances

namespace GraphSimOT.Gaps

/-- Theorem 9 (p. 9): for all graphs `G, H` of the same order,
`δ_1(G, H) ≤ 15 √(δ^OT_1(G, H) · ln(4/δ^OT_1(G, H)))`, the right-hand side being `0` when
`δ^OT_1(G, H) = 0` (Lean's value there: `0 · log 0 = 0`). -/
theorem theorem_9 {n : ℕ} (G H : SimpleGraph (Fin n)) :
    delta1 G H ≤ 15 * Real.sqrt (deltaOT1 G H * Real.log (4 / deltaOT1 G H)) := by sorry

end GraphSimOT.Gaps
