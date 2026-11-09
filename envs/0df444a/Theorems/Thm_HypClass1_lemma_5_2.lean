-- Prove2me | Theorems.Thm_HypClass1_lemma_5_2
-- name    : HypClass1.lemma_5_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T07:35:21.436271+00:00
-- url     : https://prove2.me/theorems/971a53a5-6b48-45c5-87c6-fc8dae89a489
-- title:
--   Lemma 5.2 — random bipartite structures project pseudorandom 3-graphs to pseudorandom bipartite graphs
-- statement:
--   Let $C$ be a sufficiently large constant, $n$ a positive multiple of $3$, and $\varepsilon, \eta, p, q \in [0,1]$ with
--   $$
--   n^{-1/5} \le 3\varepsilon \le \frac1{100},\qquad \eta \le \min\{\varepsilon, 1/4\},\qquad p \ge \frac{C\log n}{\varepsilon^2 n},\qquad q \ge \frac{C\log n}{\varepsilon^4 pn}.
--   $$
--   Let $H$ be a 3-graph on $n$ vertices and $\Xi_{\eta,q} = (X,Y,Z,M,E)$ a random $(\eta,q,n)$-bipartite structure on the same vertex set. Then with probability at least $1 - n^{-C^{1/3}}$ both of the following hold:
--   1. if $\deg_H(u,v) = (1\pm\varepsilon)pn$ for all $u \ne v$, then every vertex $x$ of $\Xi^{(2)}_{\eta,q}(H)$ has degree $(1\pm100\varepsilon)pqn/3$;
--   2. if $H$ is $(\varepsilon,p,n)$-pseudorandom, then $\Xi^{(2)}_{\eta,q}(H)$ is $(100\varepsilon, pq, n/3)$-pseudorandom.
--
--   **Formalization Note** The claim holds for every admissible weight function of (C3), which may depend on the outcome of (C1)–(C2). The vertices of $\Xi^{(2)}(H)$ are $M \cup Z$.
--
--   Differences from the source:
--   - reading: 'for a sufficiently large constant C' → ∃ C₀, ∀ C ≥ C₀, for every n; reason: the standard reading
--   - reading: 'with probability 1 − n^{…}' → with probability at least 1 − n^{…}; reason: the proofs conclude 'with probability at least'
--   - reading: 'a random (η, q, n)-bipartite structure' with 'a weight function φ' in (C3) → for every weight function φ, possibly depending on (X, Y, Z, M), with 0 ≤ φ ≤ 1 and φ = (1 ± η)q on M × Z; reason: Definition 5.1 does not fix φ, and the paper lets it depend on the earlier choices (Lemma 7.2); the strongest reading quantifies over all admissible φ
--   - reading: log (base not named) → natural logarithm Real.log; reason: standard convention; paper.md decision 6
-- source:
--   Chatterjee, Ferber, Sales, Shurman, Almost Every 3-Uniform Hypergraph is Class 1, manuscript (STOC 2027 submission, version of 2026-11-03, sha256 ce3bba9d…), Lemma 5.2, pp.12–13

import Mathlib
import Definitions.Def_HypClass1_K3
import Definitions.Def_HypClass1_codeg
import Definitions.Def_HypClass1_IsPseudorandom3
import Definitions.Def_HypClass1_IsPseudorandomBip
import Definitions.Def_HypClass1_bipStructProb
import Definitions.Def_HypClass1_proj2

namespace HypClass1

/-- **Lemma 5.2 (bipartification).** Chatterjee, Ferber, Sales, Shurman, *Almost Every 3-Uniform Hypergraph is Class 1*, manuscript
(STOC 2027 submission, version of 2026-11-03, sha256 ce3bba9d…), Lemma 5.2, pp.12–13:
"Let ε, η, p, q ∈ [0, 1] be real numbers and n ∈ 3Z+ be a positive integer multiple of 3 such that
n^{−1/5} ≤ 3ε ≤ 1/100, η ≤ min{ε, 1/4}, p ≥ C log n/(ε²n) and q ≥ C log n/(ε⁴pn) for a sufficiently large
constant C. Let H be a 3-graph on n vertices and Ξ_{η,q} = (X, Y, Z, M, E) be a random
(η, q, n)-bipartite structure on the same set of vertices. Then the following two statements hold with
probability 1 − n^{−C^{1/3}}:
(i) If deg_H(u, v) = (1 ± ε)pn for every u, v ∈ V(H), then deg_{Ξ^{(2)}_{η,q}(H)}(x) = (1 ± 100ε)pqn/3 for
x ∈ V(Ξ^{(2)}_{η,q}(H)).
(ii) If H is an (ε, p, n)-pseudorandom 3-graph, then the bipartite graph Ξ^{(2)}_{η,q}(H) is
(100ε, pq, n/3)-pseudorandom."

**Formalization Note.** `∃ C₀, ∀ C ≥ C₀`, every `n`. "With probability 1 − n^{−C^{1/3}}" is read as "at
least" (the proof ends so, p.15). The claim holds for every admissible weight function `φ` of (C3),
which may depend on the outcome `s = (X, Y, Z, M)` of (C1)–(C2): `0 ≤ φ ≤ 1` and `φ = (1 ± η)q` on `M × Z`.
The vertices of `Ξ^{(2)}(H)` are `M ∪ Z`; its parts `M` and `Z` have `n/3` elements. (i) and (ii) are two
implications inside one event. -/
theorem lemma_5_2 :
    ∃ C₀ : ℝ, ∀ C : ℝ, C₀ ≤ C → ∀ n : ℕ, 0 < n → 3 ∣ n →
      ∀ ε η p q : ℝ, 0 ≤ ε → ε ≤ 1 → 0 ≤ η → η ≤ 1 → 0 ≤ p → p ≤ 1 → 0 ≤ q → q ≤ 1 →
      (n : ℝ) ^ (-(1 / 5 : ℝ)) ≤ 3 * ε → 3 * ε ≤ 1 / 100 → η ≤ min ε (1 / 4) →
      C * Real.log n / (ε ^ 2 * n) ≤ p → C * Real.log n / (ε ^ 4 * p * n) ≤ q →
      ∀ H : Finset (Finset (Fin n)), H ⊆ K3 (Fin n) →
      ∀ φ : BipFrame (Fin n) → Finset (Fin n) → ℝ,
        (∀ s : BipFrame (Fin n), IsBipFrame s → ∀ e ∈ structTriples s.2.2.2 s.2.2.1,
          0 ≤ φ s e ∧ φ s e ≤ 1 ∧ (1 - η) * q ≤ φ s e ∧ φ s e ≤ (1 + η) * q) →
        1 - (n : ℝ) ^ (-C ^ (1 / 3 : ℝ)) ≤ bipStructProb φ (fun s E =>
          ((∀ u v : Fin n, u ≠ v →
              (1 - ε) * p * n ≤ codeg H u v ∧ (codeg H u v : ℝ) ≤ (1 + ε) * p * n) →
            (∀ m ∈ s.2.2.2,
              (1 - 100 * ε) * p * q * n / 3 ≤ ldeg (proj2 H s.2.2.2 s.2.2.1 E) m ∧
                (ldeg (proj2 H s.2.2.2 s.2.2.1 E) m : ℝ) ≤ (1 + 100 * ε) * p * q * n / 3) ∧
            (∀ z ∈ s.2.2.1,
              (1 - 100 * ε) * p * q * n / 3 ≤ rdeg (proj2 H s.2.2.2 s.2.2.1 E) z ∧
                (rdeg (proj2 H s.2.2.2 s.2.2.1 E) z : ℝ) ≤ (1 + 100 * ε) * p * q * n / 3)) ∧
          (IsPseudorandom3 ε p Finset.univ H →
            IsPseudorandomBip (100 * ε) (p * q) s.2.2.2 s.2.2.1 (proj2 H s.2.2.2 s.2.2.1 E))) := by sorry

end HypClass1
