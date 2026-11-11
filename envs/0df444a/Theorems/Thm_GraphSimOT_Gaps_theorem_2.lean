-- Prove2me | Theorems.Thm_GraphSimOT_Gaps_theorem_2
-- name    : GraphSimOT.Gaps.theorem_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T18:06:56.540916+00:00
-- url     : https://prove2.me/theorems/2b309eec-f39e-49f6-aa9c-ecb052caa8fb
-- title:
--   Theorem 2 (Upper Bounds) — δ_ed ≤ 2δ^OT_ed, δ_1 ≤ 15√(δ^OT_1 ln(4/δ^OT_1)), δ_□ ≤ C_ε(δ^OT_□)^{1−ε}, δ_2 ≤ (1+2√2)√δ^OT_2
-- statement:
--   For graphs $G, H$ on the same number $n$ of vertices, let $\delta_\diamond(G,H)$ be the normalised bijective distance (minimum over all bijections $\pi$ of $\|A_G^\pi - A_H\|_\diamond$, divided by $n^2$ for the entrywise 1-norm and the cut norm, by $n$ for the operator 1- and 2-norms), and $\delta^{OT}_\diamond(G,H)$ its optimal transport relaxation (minimum over fractional alignments $Q^*$, couplings of the uniform distributions, of $\|B_\diamond(G,H,Q^*)\|_\diamond$, with the convention $0^0 = 0$). Then for all pairs of graphs of the same order and all $\varepsilon>0$:
--   $$\delta_{ed}\le 2\,\delta^{OT}_{ed},\qquad \delta_1\le 15\sqrt{\delta^{OT}_1\ln(4/\delta^{OT}_1)},\qquad \delta_\square\le C_\varepsilon\,(\delta^{OT}_\square)^{1-\varepsilon},\qquad \delta_2\le(1+2\sqrt2)\sqrt{\delta^{OT}_2},$$
--   where $C_\varepsilon>0$ is a constant depending only on $\varepsilon$. All four inequalities are stated, for every $n$ (including $n = 0, 1$).
--
--   This is the paper's headline: the integrality gaps of the optimal transport relaxations of edit, local edit, cut and spectral distance are bounded uniformly, improving Pikhurko's factor $3$ for edit distance and the bound $32(\delta^{OT}_\square)^{1/67}$ for cut distance, and giving the first bounds for local edit and spectral distance. It follows from Theorems 6, 9, 11 and 14.
--
--   **Formalization Note.** At $\delta^{OT}_1 = 0$ the second right-hand side is $15\sqrt{0\cdot\ln 0} = 0$ in Lean (the convention of Theorem 9). $(\delta^{OT}_\square)^{1-\varepsilon}$ is `Real.rpow`: at $\delta^{OT}_\square = 0$ it is $0$ for $\varepsilon\ne1$ and $1$ for $\varepsilon = 1$. The constant $C_\varepsilon$ is chosen before $n$ and the graphs.
--
--   Differences from the source:
--   - encoding: graphs G, H of the same order n with vertex sets V, W → G H : SimpleGraph (Fin n); reason: every pair of graphs of order n is isomorphic to a pair on Fin n and all distances are isomorphism-invariant; the paper itself takes V(G) = V(H) = [n] in App. E.2 and F.2
--   - encoding: each of δ_ed, δ_1, δ_□, δ_2, δ^OT_ed, δ^OT_1, δ^OT_□, δ^OT_2 defined as a minimum → sInf of the costs over the fractional alignments (bijective distances: Finset.inf' over all permutations, a genuine minimum); reason: the set of costs is nonempty and bounded below by 0, and the paper shows the minimum is attained (pp. 14–15), so the infimum is the minimum
--   - encoding: δ^OT_1 ln(4/δ^OT_1) at δ^OT_1 = 0 (read as 0, Theorem 9) → Real.sqrt (δOT₁ * Real.log (4 / δOT₁)) = 0 there; reason: Real.log (4 / 0) = Real.log 0 = 0; same value as the paper's convention
--   - generalization: (δ^OT_□)^{1−ε} at δ^OT_□ = 0 with ε > 1 (0 to a negative power, +∞) → Real.rpow 0 (1 − ε) = 0, so the clause requires δ_□ = 0 there; reason: everywhere else the values agree; δ^OT_□ = 0 forces δ_□ = 0 (Theorem 11), so the Lean clause specializes to the source
-- source:
--   Breitung, Gervens, Grohe, Graph Similarity Meets Optimal Transport, arXiv:2611.05048 (held version, sha256 1cd10e91…), p. 3, Theorem 2

import Mathlib
import Definitions.Def_GraphSimOT_Gaps_Distances

namespace GraphSimOT.Gaps

/-- Theorem 2 (Upper Bounds, p. 3): for all pairs of graphs of the same order and all
`ε > 0`: `δ_ed ≤ 2 δ^OT_ed`, `δ_1 ≤ 15 √(δ^OT_1 ln(4/δ^OT_1))`, `δ_□ ≤ C_ε (δ^OT_□)^{1−ε}`
with `C_ε > 0` depending only on `ε`, and `δ_2 ≤ (1 + 2√2) √δ^OT_2`. -/
theorem theorem_2 :
    (∀ (n : ℕ) (G H : SimpleGraph (Fin n)), deltaEd G H ≤ 2 * deltaOTEd G H) ∧
    (∀ (n : ℕ) (G H : SimpleGraph (Fin n)),
      delta1 G H ≤ 15 * Real.sqrt (deltaOT1 G H * Real.log (4 / deltaOT1 G H))) ∧
    (∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (G H : SimpleGraph (Fin n)),
      deltaCut G H ≤ C * deltaOTCut G H ^ (1 - ε)) ∧
    (∀ (n : ℕ) (G H : SimpleGraph (Fin n)),
      delta2 G H ≤ (1 + 2 * Real.sqrt 2) * Real.sqrt (deltaOT2 G H)) := by sorry

end GraphSimOT.Gaps
