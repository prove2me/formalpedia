-- Prove2me | Theorems.Thm_HypClass1_lemma_6_1
-- name    : HypClass1.lemma_6_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T07:35:36.217435+00:00
-- url     : https://prove2.me/theorems/94e78419-bd81-4744-9477-a16ea8205ba0
-- title:
--   Lemma 6.1 — a randomized almost 1-factorization of a pseudorandom bipartite graph covering $R$
-- statement:
--   Let $C$ be a sufficiently large constant, $n \ge 1$, and $\varepsilon, p, \gamma \in [0,1]$ with $p \ge C\log n/(\varepsilon^2 n)$ and $\varepsilon \le C^{-2}$. Let $B$ and $R$ be disjoint bipartite graphs with parts $X, Y$, $|X| = |Y| = n$, such that $B$ is $(\varepsilon,p,n)$-pseudorandom and $R$ is $(\gamma\pm\varepsilon)pn$-regular. Then there is a randomized algorithm that with probability at least $1 - n^{-C^{1/4}}$ outputs a collection $\mathcal M$ of perfect matchings of $B \cup R$ such that:
--   1. (D1) $R \subseteq \bigcup_{M\in\mathcal M} M$;
--   2. (D2) for $\tilde R = B \setminus \bigcup_{M\in\mathcal M} M$, every vertex $x$ has $C\varepsilon pn \le \deg_{\tilde R}(x) \le 12C\varepsilon pn$;
--   3. (D3) conditioned on success, every edge $e \in B$ satisfies $C\varepsilon \le \mathbb P(e \notin \bigcup_{M\in\mathcal M} M) \le 5C\varepsilon$;
--   4. (D4) conditioned on success, for every set $A \subseteq B$ of $a$ edges, $\mathbb P(\exists M \in \mathcal M : A \subseteq M) \le \left(\frac{C\log n}{pn}\right)^{a-1}$.
--
--   **Formalization Note** Both parts are `Fin n`. The algorithm is its output law; (D1), (D2) hold for every output of positive probability, and (D3), (D4) are stated when the algorithm succeeds with positive probability.
--
--   Differences from the source:
--   - reading: 'for a sufficiently large positive constant C' → ∃ C₀, ∀ C ≥ C₀, for every n ≥ 1; reason: the standard reading
--   - reading: 'with probability 1 − n^{…}' → with probability at least 1 − n^{…}; reason: the proofs conclude 'with probability at least'
--   - reading: 'there exists a randomized algorithm that with probability … outputs …' → ∃ μ : PMF (Option _) with μ(none) ≤ the failure bound; every output of positive probability has the deterministic properties; reason: an algorithm is identified with its output law; the paper claims nothing about running time
--   - reading: (D3) 'the probability that an edge is not covered' → for every edge e ∈ B; reason: edges of R are always covered by (D1), so the lower bound Cε can only refer to edges of B
--   - reading: (D2) 'for x ∈ V(R̃)' → for every vertex of X ∪ Y; reason: R̃ is a bipartite graph on X, Y; the lower bound Cεpn > 0 makes every vertex non-isolated
--   - encoding: probabilities conditioned on success → (D3), (D4) asserted under the hypothesis that the failure probability is < 1; reason: conditioning on a null event is undefined; for n ≥ 2 the failure bound n^{−C^{1/4}} is < 1, so this excludes only n = 1 with certain failure
--   - encoding: ε ∈ [0, 1] → 0 < ε ≤ 1; reason: C log n/(ε²n) is undefined at ε = 0
--   - reading: log (base not named) → natural logarithm Real.log; reason: standard convention; paper.md decision 6
-- source:
--   Chatterjee, Ferber, Sales, Shurman, Almost Every 3-Uniform Hypergraph is Class 1, manuscript (STOC 2027 submission, version of 2026-11-03, sha256 ce3bba9d…), Lemma 6.1, pp.15–16

import Mathlib
import Definitions.Def_HypClass1_IsPseudorandomBip
import Definitions.Def_HypClass1_IsAlmostRegularBip
import Definitions.Def_HypClass1_IsPerfectMatchingBip
import Definitions.Def_HypClass1_condSucc

namespace HypClass1

/-- **Lemma 6.1 (randomized almost 1-factorization).** Chatterjee, Ferber, Sales, Shurman, *Almost Every 3-Uniform Hypergraph is Class 1*, manuscript
(STOC 2027 submission, version of 2026-11-03, sha256 ce3bba9d…), Lemma 6.1, pp.15–16:
"Let ε, p, γ ∈ [0, 1] be real numbers and n ≥ 1 an integer satisfying p ≥ C log n/(ε²n) and ε ≤ C^{−2}
for a sufficiently large positive constant C. Let B and R be disjoint bipartite graphs on the vertex
set X, Y with |X| = |Y| = n such that B is (ε, p, n)-pseudorandom and R is (γ ± ε)pn-regular. Then
there exists a randomized algorithm that with probability 1 − n^{−C^{1/4}} outputs a collection of
perfect matchings M of B ∪ R with the following properties:
(D1) The edges of R are covered by M, i.e., R ⊆ ⋃_{M∈M} M.
(D2) If R̃ := B ∖ ⋃_{M∈M} M, then for x ∈ V(R̃), we have Cεpn ≤ deg_R̃(x) ≤ 12Cεpn
(D3) Conditioned on the event that the algorithm succeeds, the probability that an edge is not
covered by a matching in M is Cε ≤ P(e ∉ ⋃_{M∈M} M) ≤ 5Cε
(D4) Conditioned on the event that the algorithm succeeds, for any set A ⊆ B of a edges, the
probability that the set A is contained in one of the matchings selected in M is
P(∃M ∈ M : A ⊆ M) ≤ (C log n/(pn))^{a−1}"

**Formalization Note.** `∃ C₀, ∀ C ≥ C₀`, every `n ≥ 1`. Both parts are `Fin n` (`X = Y = univ`), edges are
pairs `(x, y)`. The algorithm is its output law `μ : PMF (Option _)`, `none` = failure, and "with
probability 1 − n^{−C^{1/4}}" is `μ(none) ≤ n^{−C^{1/4}}`. Every output `𝓜` of positive probability is a
finite set of perfect matchings of `B ∪ R` with (D1), (D2); `V(R̃) = X ∪ Y`, so (D2) bounds the degree
of every vertex. (D3) is for every edge `e ∈ B` (an edge of `R` is always covered); (D3), (D4) are
probabilities conditioned on success (`condSucc`), required when success has positive probability.
The exponent `a − 1` is an integer (`zpow`). `ε > 0` is assumed: at `ε = 0` the hypothesis
`C log n/(ε²n)` is undefined. -/
theorem lemma_6_1 :
    ∃ C₀ : ℝ, ∀ C : ℝ, C₀ ≤ C → ∀ n : ℕ, 1 ≤ n → ∀ ε p γ : ℝ, 0 < ε → ε ≤ 1 → 0 ≤ p → p ≤ 1 →
      0 ≤ γ → γ ≤ 1 → C * Real.log n / (ε ^ 2 * n) ≤ p → ε ≤ C ^ (-2 : ℝ) →
      ∀ B R : Finset (Fin n × Fin n), Disjoint B R →
        IsPseudorandomBip ε p Finset.univ Finset.univ B →
        IsAlmostRegularBip γ ε p Finset.univ Finset.univ R →
        ∃ μ : PMF (Option (Finset (Finset (Fin n × Fin n)))),
          (μ none).toReal ≤ (n : ℝ) ^ (-C ^ (1 / 4 : ℝ)) ∧
          (∀ 𝓜, μ (some 𝓜) ≠ 0 →
            (∀ M ∈ 𝓜, M ⊆ B ∪ R ∧ IsPerfectMatchingBip Finset.univ Finset.univ M) ∧
            R ⊆ 𝓜.biUnion id ∧
            (∀ x : Fin n, C * ε * p * n ≤ ldeg (B \ 𝓜.biUnion id) x ∧
              (ldeg (B \ 𝓜.biUnion id) x : ℝ) ≤ 12 * C * ε * p * n) ∧
            (∀ y : Fin n, C * ε * p * n ≤ rdeg (B \ 𝓜.biUnion id) y ∧
              (rdeg (B \ 𝓜.biUnion id) y : ℝ) ≤ 12 * C * ε * p * n)) ∧
          ((μ none).toReal < 1 →
            (∀ e ∈ B, C * ε ≤ condSucc μ (fun 𝓜 => e ∉ 𝓜.biUnion id) ∧
              condSucc μ (fun 𝓜 => e ∉ 𝓜.biUnion id) ≤ 5 * C * ε) ∧
            (∀ A ⊆ B, condSucc μ (fun 𝓜 => ∃ M ∈ 𝓜, A ⊆ M) ≤
              (C * Real.log n / (p * n)) ^ ((A.card : ℤ) - 1))) := by sorry

end HypClass1
