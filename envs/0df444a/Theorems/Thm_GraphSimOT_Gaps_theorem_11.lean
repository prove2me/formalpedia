-- Prove2me | Theorems.Thm_GraphSimOT_Gaps_theorem_11
-- name    : GraphSimOT.Gaps.theorem_11
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T18:06:47.604654+00:00
-- url     : https://prove2.me/theorems/d2e6737b-b427-4ceb-ad9f-3c4092ea94fd
-- title:
--   Theorem 11 — δ^OT_□ ≤ δ_□ ≤ C δ^OT_□ ln(e/δ^OT_□) ln(e ln(e/δ^OT_□)); hence δ_□ = O((δ^OT_□)^{1−ε})
-- statement:
--   There is a universal constant $C>0$ such that for all graphs $G, H$ of the same order, with $\delta_\square := \delta_\square(G,H)$ and $\delta^{OT}_\square := \delta^{OT}_\square(G,H)$,
--   $$\delta^{OT}_\square\ \le\ \delta_\square\ \le\ C\,\delta^{OT}_\square\,\ln\frac{e}{\delta^{OT}_\square}\,\ln\Big(e\ln\frac e{\delta^{OT}_\square}\Big),$$
--   where the right-hand side is defined as $0$ if $\delta^{OT}_\square = 0$. Consequently, for every $\varepsilon>0$ there is $C_\varepsilon>0$, depending only on $\varepsilon$, with $\delta_\square\le C_\varepsilon(\delta^{OT}_\square)^{1-\varepsilon}$ for all graphs $G, H$ of the same order.
--
--   This improves the bound $\delta_\square\le 32(\delta^{OT}_\square)^{1/67}$ of Borgs, Chayes, Lovász, Sós and Vesztergombi towards Lovász's conjectured $\delta_\square\le 2\delta^{OT}_\square$, and is clause (iii) of Theorem 2.
--
--   **Formalization Note.** At $\delta^{OT}_\square = 0$ the Lean right-hand side is a product with the factor $0$, hence $0$. $(\delta^{OT}_\square)^{1-\varepsilon}$ is `Real.rpow`; at $\delta^{OT}_\square = 0$ it is $0$ for $\varepsilon\ne1$ and $1$ for $\varepsilon = 1$.
--
--   Differences from the source:
--   - encoding: graphs G, H of the same order n with vertex sets V, W → G H : SimpleGraph (Fin n); reason: every pair of graphs of order n is isomorphic to a pair on Fin n and all distances are isomorphism-invariant; the paper itself takes V(G) = V(H) = [n] in App. E.2 and F.2
--   - encoding: δ_□ and δ^OT_□ defined as a minimum → sInf of the costs over the fractional alignments (bijective distances: Finset.inf' over all permutations, a genuine minimum); reason: the set of costs is nonempty and bounded below by 0, and the paper shows the minimum is attained (pp. 14–15), so the infimum is the minimum
--   - encoding: the right-hand side is defined as 0 if δ^OT_□ = 0; e the Euler number → C * δOT * log (exp 1 / δOT) * log (exp 1 * log (exp 1 / δOT)), which is 0 at δOT = 0; e = Real.exp 1; reason: same values
--   - reading: Consequently, for every ε > 0 we have δ_□ = O((δ^OT_□)^{1−ε}) → ∀ ε > 0, ∃ C > 0, ∀ n G H, δ_□ ≤ C * δOT ^ (1 − ε); reason: the uniform reading, the one the proof gives ('a constant C_α > 0 depending only on α', p. 44) and Theorem 2 states
--   - generalization: (δ^OT_□)^{1−ε} at δ^OT_□ = 0 with ε > 1 (0 to a negative power, +∞) → Real.rpow 0 (1 − ε) = 0, so the clause requires δ_□ = 0 there; reason: everywhere else the values agree; δ^OT_□ = 0 forces δ_□ = 0 by the first part, so the Lean clause specializes to the source
-- source:
--   Breitung, Gervens, Grohe, Graph Similarity Meets Optimal Transport, arXiv:2611.05048 (held version, sha256 1cd10e91…), p. 10, Theorem 11

import Mathlib
import Definitions.Def_GraphSimOT_Gaps_Distances

namespace GraphSimOT.Gaps

/-- Theorem 11 (p. 10): there is a universal constant `C > 0` such that for all graphs `G, H`
of the same order, `δ^OT_□ ≤ δ_□ ≤ C δ^OT_□ ln(e/δ^OT_□) ln(e ln(e/δ^OT_□))` (the right-hand
side being `0` when `δ^OT_□ = 0`); consequently, for every `ε > 0` there is `C_ε > 0` with
`δ_□ ≤ C_ε (δ^OT_□)^{1−ε}` for all graphs of the same order. -/
theorem theorem_11 :
    (∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (G H : SimpleGraph (Fin n)),
      deltaOTCut G H ≤ deltaCut G H ∧
      deltaCut G H ≤ C * deltaOTCut G H * Real.log (Real.exp 1 / deltaOTCut G H) *
        Real.log (Real.exp 1 * Real.log (Real.exp 1 / deltaOTCut G H))) ∧
    (∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (G H : SimpleGraph (Fin n)),
      deltaCut G H ≤ C * deltaOTCut G H ^ (1 - ε)) := by sorry

end GraphSimOT.Gaps
