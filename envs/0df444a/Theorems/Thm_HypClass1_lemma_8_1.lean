-- Prove2me | Theorems.Thm_HypClass1_lemma_8_1
-- name    : HypClass1.lemma_8_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T07:34:16.635081+00:00
-- url     : https://prove2.me/theorems/1482c5e8-2eff-491f-b493-b84d2327bc13
-- title:
--   Lemma 8.1 (Stage II) — concentrating the codegrees of the remainder
-- statement:
--   Let $C$ be a sufficiently large constant and $n$ a sufficiently large integer. Let $\varepsilon, \delta, p, q, r, \lambda \in [0,1]$ and let $k$ be a positive integer with
--   $$
--   \log n \le k \le n^{0.01},\quad \varepsilon \le \frac1{k^2},\quad \delta \ge \frac{C^3}{k^2},\quad p \ge 0.01,\quad \frac{k^7\log n}{n} \le r \le \frac1{k^6},\quad q \ge C^4 k r \log^3 n,\quad \frac{C\log n}{n} \le \lambda \le \frac{r}{3k^2}. \tag{17}
--   $$
--   Let $S \subseteq [n]$ with $|S| = n/100$. Let $H$ and $R$ be edge-disjoint 3-graphs on $[n]$ such that $H$ is $(\varepsilon, p, n)$-pseudorandom, $\Delta_2(R) \le Crn$, and
--   $$
--   \deg_H(u) = \frac{pn^2}{2} \pm \lambda n^2, \qquad \deg_R(u) = \frac{rn^2}{2} \pm \lambda n^2 \qquad \text{for every } u \in [n].
--   $$
--
--   Then with probability at least $1 - n^{-\sqrt C}$ the random homogeneous 3-graph $H_q \subseteq H$ has the following property: there is a collection $\mathcal K$ of edge-disjoint matchings in $H_q \cup R$ with
--   1. (H1) $R \subseteq \bigcup_{K\in\mathcal K} K \subseteq H_q \cup R$;
--   2. (H2) $[n] \setminus V(K) \subseteq S$ for every $K \in \mathcal K$;
--   3. (H3) every $u \in S$ is missed by at most $Ckrn$ matchings of $\mathcal K$;
--   4. (H4) for $\tilde R = H_q \setminus \bigcup_{K\in\mathcal K} K$ and $\tilde r = pq + r - 2|\mathcal K|/n^2$: $\tilde r > 0$, $\deg_{\tilde R}(u) = \tilde r n^2/2 \pm 4\lambda n^2$ for every $u$, $\deg_{\tilde R}(u,v) = (1\pm\delta)\tilde r n$ for every pair $u \ne v$, and $pq - 2rk < \tilde r < pq$.
--
--   **Formalization Note** The probability is over $H_q$ only, with $H, R, S$ fixed. $|\mathcal K|$ is the number of matchings.
--
--   Differences from the source:
--   - reading: 'for a sufficiently large constant C' (and integer n) → ∃ C₀, ∀ C ≥ C₀ (then ∃ n₀, ∀ n ≥ n₀ where the source says n is large); reason: the standard reading, and the way the paper applies these results ('Let C be a constant larger than all the previous constants', p.31)
--   - reading: |S| = n/100 → S.card = n / 100 in ℕ, i.e. ⌊n/100⌋; reason: the real equation is unsatisfiable unless 100 ∣ n, which would make the lemma vacuous for most n, while the paper applies it for every n (Prop 9.5, p.50)
--   - encoding: a collection of edge disjoint matchings K → a Finset of pairwise edge-disjoint matchings; reason: by (H2) with |S| < n every matching is non-empty, and distinct non-empty edge-disjoint matchings cannot repeat, so no multiplicity is lost and |K| is the number of matchings
--   - reading: log (base not named) → natural logarithm Real.log; reason: standard convention; paper.md decision 6
-- source:
--   Chatterjee, Ferber, Sales, Shurman, Almost Every 3-Uniform Hypergraph is Class 1, manuscript (STOC 2027 submission, version of 2026-11-03, sha256 ce3bba9d…), Lemma 8.1, p.31

import Mathlib
import Definitions.Def_HypClass1_K3
import Definitions.Def_HypClass1_deg
import Definitions.Def_HypClass1_codeg
import Definitions.Def_HypClass1_maxCodeg
import Definitions.Def_HypClass1_IsMatching
import Definitions.Def_HypClass1_IsPseudorandom3
import Definitions.Def_HypClass1_randSubProb

namespace HypClass1

/-- **Lemma 8.1 (Stage II).** Chatterjee, Ferber, Sales, Shurman, *Almost Every 3-Uniform Hypergraph is Class 1*, manuscript
(STOC 2027 submission, version of 2026-11-03, sha256 ce3bba9d…), Lemma 8.1, p.31:
"Let ε, δ, p, q, r, λ ∈ [0, 1] be real numbers, and let k ∈ Z+ be a positive integer satisfying
log n ≤ k ≤ n^{0.01}, ε ≤ 1/k², δ ≥ C³/k², p ≥ 0.01, k⁷ log n/n ≤ r ≤ 1/k⁶, q ≥ C⁴kr log³ n,
C log n/n ≤ λ ≤ r/(3k²), for a sufficiently large constant C and integer n. Let S ⊆ [n] be a set with
|S| = n/100. Let H and R be edge-disjoint 3-graphs on [n] such that H is (ε, p, n)-pseudorandom and
∆₂(R) ≤ Crn. Moreover, suppose that both H and R satisfy the degree condition deg_H(u) = pn²/2 ± λn²
and deg_R(u) = rn²/2 ± λn² for every u ∈ [n]. Then, with probability at least 1 − n^{−√C}, the random
homogeneous 3-graph H_q ⊆ H satisfies the following. There exists a collection of edge disjoint
matchings K in H_q ∪ R with the properties:
(H1) The collection K covers R, i.e., R ⊆ ⋃_{K∈K} K ⊆ H_q ∪ R.
(H2) For every K ∈ K, we have [n] ∖ V(K) ⊆ S.
(H3) For every u ∈ S, the number of matchings K ∈ K missing the vertex u is at most Ckrn.
(H4) Let R̃ := H_q ∖ ⋃_{K∈K} K. Then for every pair {u, v} ⊆ [n], it holds deg_R̃(u) = r̃n²/2 ± 4λn² and
deg_R̃(u, v) = (1 ± δ)r̃n, where r̃ := pq + r − 2|K|/n² > 0. Moreover, it holds that pq − 2rk < r̃ < pq."

**Formalization Note.** `∃ C₀, ∀ C ≥ C₀, ∃ n₀, ∀ n ≥ n₀` ("sufficiently large constant C and integer
n"). The probability is over `H_q` only (`randSubProb H (fun _ => q)`), with `H, R, S` fixed. `|S| = n/100`
is natural-number division. `|K|` is the number of matchings in `K`. The degree clause of (H4) holds for
every vertex, the codegree clause for every pair `u ≠ v`. -/
theorem lemma_8_1 :
    ∃ C₀ : ℝ, ∀ C : ℝ, C₀ ≤ C → ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      ∀ ε δ p q r lam : ℝ, 0 ≤ ε → ε ≤ 1 → 0 ≤ δ → δ ≤ 1 → 0 ≤ p → p ≤ 1 → 0 ≤ q → q ≤ 1 →
        0 ≤ r → r ≤ 1 → 0 ≤ lam → lam ≤ 1 → ∀ k : ℕ, 0 < k →
        Real.log n ≤ k → (k : ℝ) ≤ (n : ℝ) ^ (0.01 : ℝ) → ε ≤ 1 / (k : ℝ) ^ 2 →
        C ^ 3 / (k : ℝ) ^ 2 ≤ δ → 0.01 ≤ p →
        (k : ℝ) ^ 7 * Real.log n / n ≤ r → r ≤ 1 / (k : ℝ) ^ 6 →
        C ^ 4 * k * r * Real.log n ^ 3 ≤ q →
        C * Real.log n / n ≤ lam → lam ≤ r / (3 * (k : ℝ) ^ 2) →
        ∀ S : Finset (Fin n), S.card = n / 100 →
        ∀ H R : Finset (Finset (Fin n)), H ⊆ K3 (Fin n) → R ⊆ K3 (Fin n) → Disjoint H R →
        IsPseudorandom3 ε p Finset.univ H → (maxCodeg R : ℝ) ≤ C * r * n →
        (∀ u : Fin n, |(deg H u : ℝ) - p * n ^ 2 / 2| ≤ lam * n ^ 2) →
        (∀ u : Fin n, |(deg R u : ℝ) - r * n ^ 2 / 2| ≤ lam * n ^ 2) →
        1 - (n : ℝ) ^ (-Real.sqrt C) ≤ randSubProb H (fun _ => q) (fun Hq =>
          ∃ 𝒦 : Finset (Finset (Finset (Fin n))),
            (∀ K ∈ 𝒦, K ⊆ Hq ∪ R ∧ IsMatching K) ∧
            (∀ K ∈ 𝒦, ∀ K' ∈ 𝒦, K ≠ K' → Disjoint K K') ∧
            R ⊆ 𝒦.biUnion id ∧
            (∀ K ∈ 𝒦, Finset.univ \ verts K ⊆ S) ∧
            (∀ u ∈ S, ((𝒦.filter (fun K => u ∉ verts K)).card : ℝ) ≤ C * k * r * n) ∧
            ∃ rt : ℝ, rt = p * q + r - 2 * 𝒦.card / (n : ℝ) ^ 2 ∧ 0 < rt ∧
              (∀ u : Fin n,
                |(deg (Hq \ 𝒦.biUnion id) u : ℝ) - rt * n ^ 2 / 2| ≤ 4 * lam * n ^ 2) ∧
              (∀ u v : Fin n, u ≠ v →
                (1 - δ) * rt * n ≤ codeg (Hq \ 𝒦.biUnion id) u v ∧
                  (codeg (Hq \ 𝒦.biUnion id) u v : ℝ) ≤ (1 + δ) * rt * n) ∧
              p * q - 2 * r * k < rt ∧ rt < p * q) := by sorry

end HypClass1
