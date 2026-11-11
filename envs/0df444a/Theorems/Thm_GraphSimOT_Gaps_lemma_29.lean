-- Prove2me | Theorems.Thm_GraphSimOT_Gaps_lemma_29
-- name    : GraphSimOT.Gaps.lemma_29
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T18:07:51.804689+00:00
-- url     : https://prove2.me/theorems/45b8b6cc-e0ee-4522-b453-3362da89828e
-- title:
--   Lemma 29 — supp(Q) pairs are 2L-close to σ; L < 1 makes σ an isomorphism; non-isomorphic graphs have L ≥ 1
-- statement:
--   Standing hypotheses of App. D.2: $G, H$ are graphs on $[n]$, $L := d^{OT}_1(G,H)$, $Q\in\mathrm{DS}(n)$ is optimal, i.e. the local cost $L_Q(v,w) = \sum_{(v',w')}|A_G(v,v') - A_H(w,w')|Q(v',w')$ satisfies $L_Q(v,w)\le L$ for all $(v,w)\in\mathrm{supp}(Q)$, and $\sigma$ is a bijection whose graph lies in $\mathrm{supp}(Q)$ (Eq. (18): $Q(v,\sigma(v))>0$ for all $v$). With $\rho_H(w,w') = |N_H(w)\triangle N_H(w')|$:
--
--   1. if $Q(v,w)>0$ then $$\rho_H(\sigma(v), w)\le 2L;$$
--   2. if $L<1$, then $\sigma$ is an isomorphism from $G$ to $H$ ($vv'\in E(G)\iff\sigma(v)\sigma(v')\in E(H)$);
--   3. in particular, if $G$ and $H$ are not isomorphic, then $L\ge1$.
--
--   The lemma says an optimal fractional alignment only matches vertices whose images have nearly equal neighbourhoods; it is used to bound the error of closing paths into cycles in Proposition 32 and to dispose of the case $L<1$ in Theorem 9.
--
--   Differences from the source:
--   - encoding: graphs G, H of the same order n with vertex sets V, W → G H : SimpleGraph (Fin n); reason: every pair of graphs of order n is isomorphic to a pair on Fin n and all distances are isomorphism-invariant; the paper itself takes V(G) = V(H) = [n] in App. E.2 and F.2
--   - encoding: L := d^OT_1(G, H), Q ∈ DS(V, W) optimal, i.e. L_Q(v, w) ≤ L on supp(Q), and σ ∈ Bij(V, W) with Q(v, σ(v)) > 0 and L_Q(v, σ(v)) ≤ L (Eq. (18)) → hypotheses hQ : Q ∈ doublyStochastic ℝ (Fin n), hQopt : ∀ v w, 0 < Q v w → localCost G H Q v w ≤ dOT1 G H, hσ : ∀ v, 0 < Q v (σ v); reason: the section's standing hypotheses; the second half of Eq. (18) follows from hQopt and hσ, so it is not repeated
--   - encoding: d^OT_1 defined as a minimum → sInf of the costs over the fractional alignments (bijective distances: Finset.inf' over all permutations, a genuine minimum); reason: the set of costs is nonempty and bounded below by 0, and the paper shows the minimum is attained (pp. 14–15), so the infimum is the minimum
--   - encoding: σ is an isomorphism from G to H; G and H are not isomorphic → ∀ v v', G.Adj v v' ↔ H.Adj (σ v) (σ v'); IsEmpty (G ≃g H); reason: the definitions of a graph isomorphism and of non-isomorphic graphs
-- source:
--   Breitung, Gervens, Grohe, Graph Similarity Meets Optimal Transport, arXiv:2611.05048 (held version, sha256 1cd10e91…), p. 28, Lemma 29 (standing hypotheses p. 28, Eq. (18))

import Mathlib
import Definitions.Def_GraphSimOT_Gaps_Distances
import Definitions.Def_GraphSimOT_Gaps_LocalEdit

namespace GraphSimOT.Gaps

/-- Lemma 29 (App. D.2, p. 28), under the standing hypotheses of App. D.2: `L = d^OT_1(G, H)`,
`Q ∈ DS(n)` optimal (`L_Q(v, w) ≤ L` on `supp(Q)`), and `σ` a bijection whose graph lies in
`supp(Q)` (Eq. (18)). If `Q(v, w) > 0` then `ρ_H(σ(v), w) ≤ 2L`; if `L < 1` then `σ` is an
isomorphism from `G` to `H`; if `G` and `H` are not isomorphic then `L ≥ 1`. -/
theorem lemma_29 {n : ℕ} (G H : SimpleGraph (Fin n)) (Q : Matrix (Fin n) (Fin n) ℝ)
    (hQ : Q ∈ doublyStochastic ℝ (Fin n))
    (hQopt : ∀ v w, 0 < Q v w → localCost G H Q v w ≤ dOT1 G H)
    (σ : Equiv.Perm (Fin n)) (hσ : ∀ v, 0 < Q v (σ v)) :
    (∀ v w, 0 < Q v w → (rhoH H (σ v) w : ℝ) ≤ 2 * dOT1 G H) ∧
    (dOT1 G H < 1 → ∀ v v', (G.Adj v v' ↔ H.Adj (σ v) (σ v'))) ∧
    (IsEmpty (G ≃g H) → 1 ≤ dOT1 G H) := by sorry

end GraphSimOT.Gaps
