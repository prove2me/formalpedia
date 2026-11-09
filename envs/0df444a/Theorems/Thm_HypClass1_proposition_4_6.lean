-- Prove2me | Theorems.Thm_HypClass1_proposition_4_6
-- name    : HypClass1.proposition_4_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T07:34:27.865768+00:00
-- url     : https://prove2.me/theorems/02dcf25b-a30b-4f30-bc0f-975ac3df4a62
-- title:
--   Proposition 4.6 — $H_q$ of an $(\varepsilon,p,n)$-pseudorandom $H$ is $(\delta,pq,n)$-pseudorandom
-- statement:
--   Let $C > 0$ be a sufficiently large constant and let $p, q, \varepsilon, \delta \in [0,1]$ satisfy
--   $$
--   pq \ge \frac{C\log n}{\delta^4 n} \qquad\text{and}\qquad \varepsilon < \frac\delta4 .
--   $$
--   Let $H$ be an $(\varepsilon,p,n)$-pseudorandom 3-graph on $n$ vertices. Then with probability at least $1 - n^{-\sqrt C}$ the random homogeneous 3-graph $H_q$ (each edge of $H$ kept independently with probability $q$) is $(\delta, pq, n)$-pseudorandom.
--
--   **Formalization Note** The vertex set is `Fin n`. $\delta > 0$ follows from $0 \le \varepsilon < \delta/4$.
--
--   Differences from the source:
--   - reading: 'for a sufficiently large constant C > 0' → ∃ C₀ > 0, ∀ C ≥ C₀, for every n; reason: the standard reading
--   - reading: log (base not named) → natural logarithm Real.log; reason: standard convention; paper.md decision 6
-- source:
--   Chatterjee, Ferber, Sales, Shurman, Almost Every 3-Uniform Hypergraph is Class 1, manuscript (STOC 2027 submission, version of 2026-11-03, sha256 ce3bba9d…), Proposition 4.6, p.10

import Mathlib
import Definitions.Def_HypClass1_randSubProb
import Definitions.Def_HypClass1_IsPseudorandom3

namespace HypClass1

/-- **Proposition 4.6 (random homogeneous subgraphs of pseudorandom 3-graphs).** Chatterjee, Ferber, Sales, Shurman, *Almost Every 3-Uniform Hypergraph is Class 1*, manuscript
(STOC 2027 submission, version of 2026-11-03, sha256 ce3bba9d…), Proposition 4.6,
p.10: "Let p, q, ε, δ ∈ [0, 1] be real numbers such that pq ≥ C log n/(δ⁴n) for a sufficiently large
constant C > 0 and ε < δ/4. Let H be an (ε, p, n)-pseudorandom 3-graph on n vertices. Then with
probability at least 1 − n^{−√C} the 3-graph H_q is (δ, pq, n)-pseudorandom."

**Formalization Note.** `∃ C₀ > 0, ∀ C ≥ C₀`, every `n`. The vertex set is `Fin n`. `H_q` keeps each edge of
`H` independently with probability `q` (`randSubProb H (fun _ => q)`). `δ > 0` follows from `0 ≤ ε < δ/4`. -/
theorem proposition_4_6 :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ C : ℝ, C₀ ≤ C → ∀ n : ℕ, ∀ p q ε δ : ℝ, 0 ≤ p → p ≤ 1 → 0 ≤ q → q ≤ 1 →
      0 ≤ ε → ε ≤ 1 → 0 ≤ δ → δ ≤ 1 →
      C * Real.log n / (δ ^ 4 * n) ≤ p * q → ε < δ / 4 →
      ∀ H : Finset (Finset (Fin n)), IsPseudorandom3 ε p Finset.univ H →
        1 - (n : ℝ) ^ (-Real.sqrt C) ≤
          randSubProb H (fun _ => q) (fun Hq => IsPseudorandom3 δ (p * q) Finset.univ Hq) := by sorry

end HypClass1
