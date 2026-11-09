-- Prove2me | Theorems.Thm_HypClass1_lemma_6_5
-- name    : HypClass1.lemma_6_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T07:41:54.172043+00:00
-- url     : https://prove2.me/theorems/c075e9b5-8bbb-4bf3-8164-c01e3efc5f58
-- title:
--   Lemma 6.5 — a randomized near-uniform perfect matching of a pseudorandom 3-graph
-- statement:
--   Let $C > 0$ be a sufficiently large constant, $n$ a positive multiple of $3$, and $\varepsilon, p \in [0,1]$ with $n^{-1/5} \le \varepsilon \le C^{-3}$ and $p \ge C\log n/(\varepsilon^2 n)$. Let $H$ be an $(\varepsilon,p,n)$-pseudorandom 3-graph on $n$ vertices. Then there is a randomized algorithm that with probability at least $1 - n^{-C^{1/5}}$ outputs a perfect matching $M$ of $H$ such that, conditioned on success:
--   1. (E1) $\mathbb P(e \in M) = 2(1\pm10C\varepsilon)/(pn^2)$ for every edge $e \in H$;
--   2. (E2) $\mathbb P(\exists e \in M : \{u,v\} \subseteq e) = 2(1\pm10C\varepsilon)/n$ for every pair $u \ne v$;
--   3. (E3) $\mathbb P(A \subseteq M) \le \left(\frac{9C\log n}{pn^2}\right)^{a}$ for every set $A \subseteq H$ of $a$ edges.
--
--   **Formalization Note** The algorithm is its output law; every output of positive probability is a matching contained in $H$ covering all $n$ vertices.
--
--   Differences from the source:
--   - reading: 'for a sufficiently large constant C > 0' → ∃ C₀ > 0, ∀ C ≥ C₀, for every n; reason: the standard reading
--   - reading: 'there exists a randomized algorithm that with probability … outputs …' → ∃ μ : PMF (Option _) with μ(none) ≤ the failure bound; every output of positive probability has the deterministic properties; reason: an algorithm is identified with its output law; the paper claims nothing about running time
--   - reading: (E1)–(E3) probabilities with no conditioning stated → probabilities conditioned on success; reason: M is defined only when the algorithm succeeds; Lemmas 6.1 and 8.7 state the same kind of property conditioned on success
--   - reading: log (base not named) → natural logarithm Real.log; reason: standard convention; paper.md decision 6
-- source:
--   Chatterjee, Ferber, Sales, Shurman, Almost Every 3-Uniform Hypergraph is Class 1, manuscript (STOC 2027 submission, version of 2026-11-03, sha256 ce3bba9d…), Lemma 6.5, p.21

import Mathlib
import Definitions.Def_HypClass1_IsMatching
import Definitions.Def_HypClass1_IsPseudorandom3
import Definitions.Def_HypClass1_condSucc

namespace HypClass1

/-- **Lemma 6.5 (a randomized near-uniform perfect matching).** Chatterjee, Ferber, Sales, Shurman, *Almost Every 3-Uniform Hypergraph is Class 1*, manuscript
(STOC 2027 submission, version of 2026-11-03, sha256 ce3bba9d…), Lemma 6.5, p.21:
"Let ε, p ∈ [0, 1] be real numbers and let n ∈ 3Z+ be a positive integer multiple of 3 such that
n^{−1/5} ≤ ε ≤ C^{−3} and p ≥ C log n/(ε²n) for a sufficiently large constant C > 0. Let H be an
(ε, p, n)-pseudorandom 3-graph on n vertices. Then there exists a randomized algorithm that with
probability at least 1 − n^{−C^{1/5}} outputs a perfect matching M of H satisfying the following
properties:
(E1) For every edge e ∈ H, it holds that P(e ∈ M) = 2(1 ± 10Cε)/pn².
(E2) For every pair {u, v} ⊆ V(H), the probability that there exists an edge e ∈ M containing {u, v}
satisfies P(∃e ∈ M : {u, v} ⊆ e) = 2(1 ± 10Cε)/n.
(E3) For every set of edges A ⊆ H of size a, it holds that P(A ⊆ M) ≤ (9C log n/(pn²))^a."

**Formalization Note.** `∃ C₀ > 0, ∀ C ≥ C₀`, every `n`. Vertex set `Fin n`. The algorithm is its output
law `μ : PMF (Option _)`, `none` = failure; every output of positive probability is a perfect matching of
`H` (a matching contained in `H` covering every vertex). (E1)–(E3) are probabilities conditioned on
success (`condSucc`), as in Lemma 6.1 and Lemma 8.7. `2(1 ± 10Cε)/pn²` is `2(1 ± 10Cε)/(pn²)`. -/
theorem lemma_6_5 :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ C : ℝ, C₀ ≤ C → ∀ n : ℕ, 0 < n → 3 ∣ n →
      ∀ ε p : ℝ, 0 ≤ ε → ε ≤ 1 → 0 ≤ p → p ≤ 1 →
      (n : ℝ) ^ (-(1 / 5 : ℝ)) ≤ ε → ε ≤ C ^ (-3 : ℝ) → C * Real.log n / (ε ^ 2 * n) ≤ p →
      ∀ H : Finset (Finset (Fin n)), IsPseudorandom3 ε p Finset.univ H →
        ∃ μ : PMF (Option (Finset (Finset (Fin n)))),
          (μ none).toReal ≤ (n : ℝ) ^ (-C ^ (1 / 5 : ℝ)) ∧
          (∀ M, μ (some M) ≠ 0 → M ⊆ H ∧ IsMatching M ∧ verts M = Finset.univ) ∧
          (∀ e ∈ H, 2 * (1 - 10 * C * ε) / (p * n ^ 2) ≤ condSucc μ (fun M => e ∈ M) ∧
            condSucc μ (fun M => e ∈ M) ≤ 2 * (1 + 10 * C * ε) / (p * n ^ 2)) ∧
          (∀ u v : Fin n, u ≠ v →
            2 * (1 - 10 * C * ε) / n ≤ condSucc μ (fun M => ∃ e ∈ M, u ∈ e ∧ v ∈ e) ∧
              condSucc μ (fun M => ∃ e ∈ M, u ∈ e ∧ v ∈ e) ≤ 2 * (1 + 10 * C * ε) / n) ∧
          (∀ A ⊆ H, condSucc μ (fun M => A ⊆ M) ≤ (9 * C * Real.log n / (p * n ^ 2)) ^ A.card) := by sorry

end HypClass1
