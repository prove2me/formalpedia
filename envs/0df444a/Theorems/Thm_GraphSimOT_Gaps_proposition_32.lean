-- Prove2me | Theorems.Thm_GraphSimOT_Gaps_proposition_32
-- name    : GraphSimOT.Gaps.proposition_32
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T18:07:15.479767+00:00
-- url     : https://prove2.me/theorems/2ce4e375-7d9c-4404-bce9-351364156909
-- title:
--   Proposition 32 — d_1 ≤ 2L + 10 ln(4n)/γ + 2γn + n/ℓ + 2ℓL for L = d^OT_1 > 0
-- statement:
--   Standing hypotheses of App. D.2: $G, H$ are graphs on $[n]$, $L := d^{OT}_1(G,H)$ is the unnormalised optimal transport local edit distance, and $Q\in\mathrm{DS}(n)$ is optimal ($L_Q(v,w)\le L$ for all $(v,w)\in\mathrm{supp}(Q)$). Suppose $L>0$. Then for all $\gamma\in(0,\frac12]$ and all integers $\ell\ge1$,
--   $$d_1(G,H)\ \le\ 2L + \frac{10\ln(4n)}{\gamma} + 2\gamma n + \frac n\ell + 2\ell L,$$
--   where $d_1(G,H) = \min_\pi\|A_G^\pi - A_H\|_1$ is the unnormalised local edit distance.
--
--   The bound is obtained by rounding $Q$ to a bijection; balancing $\gamma$ and $\ell$ gives Theorem 9.
--
--   Differences from the source:
--   - encoding: graphs G, H of the same order n with vertex sets V, W → G H : SimpleGraph (Fin n); reason: every pair of graphs of order n is isomorphic to a pair on Fin n and all distances are isomorphism-invariant; the paper itself takes V(G) = V(H) = [n] in App. E.2 and F.2
--   - encoding: L := d^OT_1(G, H) and Q ∈ DS(V, W) optimal (L_Q ≤ L on supp(Q)); σ fixed by Eq. (18) → hypotheses hQ, hQopt as in Lemma 29; σ is not a hypothesis; reason: the section's standing hypotheses; σ does not occur in the statement and exists for every Q ∈ DS(n) by Eq. (3)
--   - encoding: d^OT_1 defined as a minimum → sInf of the costs over the fractional alignments (bijective distances: Finset.inf' over all permutations, a genuine minimum); reason: the set of costs is nonempty and bounded below by 0, and the paper shows the minimum is attained (pp. 14–15), so the infimum is the minimum
--   - encoding: ℓ ∈ ℕ_{>0} → ℓ : ℕ with 0 < ℓ, cast to ℝ; reason: same values
-- source:
--   Breitung, Gervens, Grohe, Graph Similarity Meets Optimal Transport, arXiv:2611.05048 (held version, sha256 1cd10e91…), p. 29, Proposition 32 (standing hypotheses p. 28)

import Mathlib
import Definitions.Def_GraphSimOT_Gaps_Distances

namespace GraphSimOT.Gaps

/-- Proposition 32 (App. D.2, p. 29), under the standing hypotheses of App. D.2
(`L = d^OT_1(G, H)`, `Q ∈ DS(n)` optimal): if `L > 0`, then for all `γ ∈ (0, 1/2]` and
`ℓ ∈ ℕ_{>0}`, `d_1(G, H) ≤ 2L + 10 ln(4n)/γ + 2γn + n/ℓ + 2ℓL`. -/
theorem proposition_32 {n : ℕ} (G H : SimpleGraph (Fin n)) (Q : Matrix (Fin n) (Fin n) ℝ)
    (hQ : Q ∈ doublyStochastic ℝ (Fin n))
    (hQopt : ∀ v w, 0 < Q v w → localCost G H Q v w ≤ dOT1 G H)
    (hL : 0 < dOT1 G H) (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ ≤ 1 / 2) (ℓ : ℕ) (hℓ : 0 < ℓ) :
    d1 G H ≤ 2 * dOT1 G H + 10 * Real.log (4 * n) / γ + 2 * γ * n + (n : ℝ) / ℓ
      + 2 * ℓ * dOT1 G H := by sorry

end GraphSimOT.Gaps
