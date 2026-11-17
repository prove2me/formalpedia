-- Prove2me | Theorems.Thm_MonoidProdQ_Supplement_theorem_25
-- name    : MonoidProdQ.Supplement.theorem_25
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T11:18:20.129251+00:00
-- url     : https://prove2.me/theorems/a0fe35a3-f50b-4aba-aede-bd717bb8cb64
-- title:
--   Theorem 25 — general index $k$: $\beta_G(M)\le C(k+1)(\log_2|M|+1)\log(\log_2|M|+2)$
-- statement:
--   There are absolute constants such that the following holds for every $k\ge1$, every finite commutative monoid $M$ with $x^{k+1}=x^k$ for all $x\in M$, and every $G\subseteq M$:
--
--   1. $\beta_G(M)$ is finite and $$\beta_G(M)\le C(k+1)\bigl(\log_2|M|+1\bigr)\log\bigl(\log_2|M|+2\bigr);\tag{27}$$
--   2. for every $n\ge1$, $$\mathrm{ADV}^\pm(\mathrm{Prod}_{M,G,n})\le C'\sqrt{n\min\{n,\ k\log(|M|+1)\log\log(|M|+2)\}};\tag{28}$$
--   3. the same expression, with a universal constant, upper-bounds $Q_{1/3}(\mathrm{Prod}_{M,G,n})$.
--
--   **Formalization Note** $\log$ is natural and $\log_2$ base two (Conventions, p.23); $\log\log(|M|+2)$ is $\log(\log(|M|+2))$, which is positive since $\log 3>1$. Each clause has its own constant, chosen before $k$, $M$, $G$ and $n$.
--
--   Differences from the source:
--
--   - encoding: an absolute constant C in (27); O(·) in (28) and for Q_{1/3} → ∃ C > 0 chosen before k, M, G, n, one per clause; reason: absolute constants; the O-bounds follow from (27) via the published Theorem 18, whose constants are universal
--   - encoding: β_G(M) ≤ … with β_G(M) ∈ ℕ ∪ {∞} → β_G(M) ≠ ⊤ and its natural value compared with the real bound; reason: the bound forces finiteness
--   - encoding: n ≥ 1 input positions (standing assumption, p.21) → 1 ≤ n as a hypothesis; reason: with no position the platform's query register is empty and Q_{1/3} is the undefined value ⊤
-- source:
--   Lee–Santha, The quantum query complexity of the semigroup product problem, arXiv:2609.39974 (held version, sha256 9eec405d…ffb6), Theorem 25 (General index k), p.38

import Definitions.Def_MonoidProdQ_productBreadth
import Definitions.Def_MonoidProdQ_prodMap
import Definitions.Def_MonoidProdQ_advPm
import Definitions.Def_MonoidProdQ_Q13

open scoped ENNReal

universe u

namespace MonoidProdQ.Supplement

/-- Lee–Santha, *The quantum query complexity of the semigroup product problem*,
arXiv:2609.39974 (held version, sha256 9eec405d…ffb6), Theorem 25 (General index k), p.38: "Let
k ≥ 1, let M be a finite commutative monoid satisfying x^{k+1} = x^k for every x ∈ M, and let
G ⊆ M. There is an absolute constant C such that
β_G(M) ≤ C(k + 1)(log₂|M| + 1) log(log₂|M| + 2). (27) Consequently
ADV±(Prod_{M,G,n}) = O(√(n min{n, k log(|M| + 1) log log(|M| + 2)})). (28) The same asymptotic
expression upper-bounds Q_{1/3}(Prod_{M,G,n})." Three conjuncts, each with its own constant
chosen before `k`, `M`, `G` and `n`: Eq. (27) (with finiteness of `β_G(M)`); Eq. (28) for
`n ≥ 1`; the same bound for `Q_{1/3}`.

**Formalization Note.** `log₂` is `Real.logb 2`, the bare `log` natural (Conventions, p.23), and
`log log(|M| + 2)` is `log(log(|M| + 2))`, positive since `log 3 > 1`. The minimum is taken in
`ℝ`. `β_G(M) = productBreadth G ∈ ℕ∞` is compared after `toNat`, its finiteness asserted first.
The `O` constants are universal: Eq. (28) follows from Eq. (27) by the published Theorem 18,
whose constants are universal. -/
theorem theorem_25 :
    (∃ C : ℝ, 0 < C ∧
      ∀ (k : ℕ), 1 ≤ k → ∀ (M : Type u) [CommMonoid M] [Fintype M] [DecidableEq M],
        (∀ x : M, x ^ (k + 1) = x ^ k) → ∀ G : Finset M, productBreadth G ≠ ⊤ ∧
          ((productBreadth G).toNat : ℝ) ≤
            C * (k + 1) * (Real.logb 2 (Fintype.card M) + 1) *
              Real.log (Real.logb 2 (Fintype.card M) + 2)) ∧
    (∃ C : ℝ, 0 < C ∧
      ∀ (k : ℕ), 1 ≤ k → ∀ (M : Type u) [CommMonoid M] [Fintype M] [DecidableEq M],
        (∀ x : M, x ^ (k + 1) = x ^ k) → ∀ (G : Finset M) (n : ℕ), 1 ≤ n →
          advPm (prodMap G n) Finset.univ ≤
            ENNReal.ofReal (C * Real.sqrt (n * min (n : ℝ)
              (k * Real.log (Fintype.card M + 1) * Real.log (Real.log (Fintype.card M + 2)))))) ∧
    (∃ C : ℝ, 0 < C ∧
      ∀ (k : ℕ), 1 ≤ k → ∀ (M : Type u) [CommMonoid M] [Fintype M] [DecidableEq M],
        (∀ x : M, x ^ (k + 1) = x ^ k) → ∀ (G : Finset M) (n : ℕ), 1 ≤ n →
          (Q13 (prodMap G n) Finset.univ : ℝ≥0∞) ≤
            ENNReal.ofReal (C * Real.sqrt (n * min (n : ℝ)
              (k * Real.log (Fintype.card M + 1) * Real.log (Real.log (Fintype.card M + 2)))))) := by sorry

end MonoidProdQ.Supplement
