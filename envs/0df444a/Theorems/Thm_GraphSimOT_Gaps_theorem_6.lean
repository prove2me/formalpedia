-- Prove2me | Theorems.Thm_GraphSimOT_Gaps_theorem_6
-- name    : GraphSimOT.Gaps.theorem_6
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T18:06:59.960905+00:00
-- url     : https://prove2.me/theorems/c4c8aa69-2a55-4a80-b647-fb62f31d8d92
-- title:
--   Theorem 6 — every Birkhoff decomposition averages to at most 2C_ed(Q); hence d_ed ≤ 2 d^OT_ed
-- statement:
--   Let $G, H$ be graphs of the same order $n$ and $Q\in\mathrm{DS}(n)$ a doubly stochastic matrix with a Birkhoff decomposition (Eq. (3)) $Q = \sum_{i=1}^m\lambda_i P_{\pi_i}$, $\lambda_i>0$, $\sum_i\lambda_i = 1$, where $P_\pi$ is the permutation matrix of the bijection $\pi$ ($P_\pi(v,w) = 1$ iff $\pi(v) = w$). With the edit costs $C_{ed}(\pi) = \|A_G^\pi - A_H\|_{ed}$ and $C_{ed}(Q) = \sum_{v,v',w,w'}|A_G(v,v') - A_H(w,w')|\,Q(v,w)Q(v',w')$,
--   $$\sum_{i=1}^m\lambda_i\,C_{ed}(\pi_i)\ \le\ 2\,C_{ed}(Q).$$
--   In particular $d_{ed}(G,H)\le 2\,d^{OT}_{ed}(G,H)$ for all graphs $G, H$ of the same order.
--
--   This is the edit-distance case of the paper's upper bounds: rounding a fractional alignment to a random bijection of its Birkhoff decomposition loses at most a factor $2$, improving Pikhurko's factor $3$.
--
--   Differences from the source:
--   - encoding: graphs G, H of the same order n with vertex sets V, W → G H : SimpleGraph (Fin n); reason: every pair of graphs of order n is isomorphic to a pair on Fin n and all distances are isomorphism-invariant; the paper itself takes V(G) = V(H) = [n] in App. E.2 and F.2
--   - encoding: a decomposition Q = Σ_{i=1}^m λ_i P_{π_i} as in Eq. (3) → m : ℕ, lam : Fin m → ℝ, π : Fin m → Equiv.Perm (Fin n) with ∀ i, 0 < lam i, Σ lam = 1 and Q = Σ lam i • (π i).permMatrix ℝ; reason: Mathlib's permMatrix σ has entry (i, j) equal to 1 iff σ i = j, the paper's P_π
--   - encoding: d^OT_ed defined as a minimum → sInf of the costs over the fractional alignments (bijective distances: Finset.inf' over all permutations, a genuine minimum); reason: the set of costs is nonempty and bounded below by 0, and the paper shows the minimum is attained (pp. 14–15), so the infimum is the minimum
-- source:
--   Breitung, Gervens, Grohe, Graph Similarity Meets Optimal Transport, arXiv:2611.05048 (held version, sha256 1cd10e91…), p. 7, Theorem 6

import Mathlib
import Definitions.Def_GraphSimOT_Gaps_Distances

namespace GraphSimOT.Gaps

/-- Theorem 6 (p. 7): for every `Q ∈ DS(n)` and every decomposition `Q = ∑ λ_i P_{π_i}` as in
Eq. (3) (`λ_i > 0`, `∑ λ_i = 1`), `∑ λ_i C_ed(π_i) ≤ 2 C_ed(Q)`; in particular
`d_ed(G, H) ≤ 2 d^OT_ed(G, H)`. -/
theorem theorem_6 :
    (∀ (n : ℕ) (G H : SimpleGraph (Fin n)) (Q : Matrix (Fin n) (Fin n) ℝ),
      Q ∈ doublyStochastic ℝ (Fin n) →
      ∀ (m : ℕ) (lam : Fin m → ℝ) (π : Fin m → Equiv.Perm (Fin n)),
        (∀ i, 0 < lam i) → ∑ i, lam i = 1 → Q = ∑ i, lam i • (π i).permMatrix ℝ →
        ∑ i, lam i * costEdPerm G H (π i) ≤ 2 * costEd G H Q) ∧
    (∀ (n : ℕ) (G H : SimpleGraph (Fin n)), dEd G H ≤ 2 * dOTEd G H) := by sorry

end GraphSimOT.Gaps
