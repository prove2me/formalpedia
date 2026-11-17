-- Prove2me | Theorems.Thm_MonoidProdQ_Supplement_theorem_80
-- name    : MonoidProdQ.Supplement.theorem_80
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T11:26:04.636505+00:00
-- url     : https://prove2.me/theorems/6c6bca86-b85d-4bd0-97d9-866af1aa8354
-- title:
--   Theorem 80 — worst-case aperiodic envelope $Q_{\mathrm{ap}}(N,n)$
-- statement:
--   Let $L(n)=2+\log_2(n+2)$ and let $Q_{\mathrm{ap}}(N,n)$ be the largest $Q_{1/3}(\mathrm{Prod}_{M,n})$ over finite aperiodic monoids $M$ of order at most $N$.
--
--   1. There is a universal $C>0$ such that for all $N,n\ge1$,
--   $$Q_{\mathrm{ap}}(N,n)\le\min\Bigl\{n,\ \sqrt n\,2^{CN^{1/3}}L(n)^{CN^{1/3}\log^{1/3}(N+2)}\Bigr\}.$$
--   2. There are universal $a,b>0$ and an integer $N_0$ such that whenever $N_0\le N\le a(\log(n+2))^3$,
--   $$Q_{\mathrm{ap}}(N,n)\ge\sqrt n\,2^{bN^{1/3}}.$$
--
--   So in this regime the factor $2^{\Theta(N^{1/3})}$ is optimal.
--
--   **Formalization Note** The maximum over representatives of isomorphism classes is expressed by quantifiers: the upper bound for every finite aperiodic monoid with $|M|\le N$, the lower bound for some such monoid. $\log$ is natural; $\log^{1/3}(N+2)=(\log(N+2))^{1/3}$.
--
--   Differences from the source:
--
--   - encoding: Q_ap(N, n) = max over representatives 𝔄_N of isomorphism classes → ∀ M with |M| ≤ N (upper bound); ∃ M with |M| ≤ N (lower bound); reason: Q_{1/3} is invariant under isomorphism, so these are the max ≤ and max ≥ statements
--   - encoding: n ≥ 1 input positions (standing assumption, p.21) → 1 ≤ n as a hypothesis; reason: with no position the platform's query register is empty and Q_{1/3} is the undefined value ⊤
-- source:
--   Lee–Santha, The quantum query complexity of the semigroup product problem, arXiv:2609.39974 (held version, sha256 9eec405d…ffb6), Theorem 80 (Worst-case aperiodic envelope), p.96

import Definitions.Def_MonoidProdQ_IsAperiodic
import Definitions.Def_MonoidProdQ_prodMap
import Definitions.Def_MonoidProdQ_Q13

open scoped ENNReal

universe u

namespace MonoidProdQ.Supplement

/-- Lee–Santha, *The quantum query complexity of the semigroup product problem*,
arXiv:2609.39974 (held version, sha256 9eec405d…ffb6), Theorem 80 (Worst-case aperiodic
envelope), p.96, with `L(n) = 2 + log₂(n + 2)` (§11, p.79; also p.17) and, for `N, n ≥ 1`,
`Q_ap(N, n) = max{Q_{1/3}(Prod_{M,n}) : M ∈ 𝔄_N}`, `𝔄_N` "a fixed set of representatives of the
isomorphism classes of finite aperiodic monoids of order at most N" (p.96): "There is a
universal constant C > 0 such that, for all N, n ≥ 1,
Q_ap(N, n) ≤ min{n, √n 2^{CN^{1/3}} L(n)^{CN^{1/3} log^{1/3}(N+2)}}. Moreover, there are universal
constants a, b > 0 and an integer N₀ such that, whenever N₀ ≤ N ≤ a(log(n + 2))³, one has
Q_ap(N, n) ≥ √n 2^{bN^{1/3}}." Two conjuncts:

1. one universal `C > 0` such that every finite aperiodic monoid `M` with `|M| ≤ N` has
   `Q_{1/3}(Prod_{M,n}) ≤ min{n, √n 2^{CN^{1/3}} L(n)^{CN^{1/3} (log(N+2))^{1/3}}}`;
2. universal `a, b > 0` and `N₀ ∈ ℕ` such that whenever `N, n ≥ 1` and
   `N₀ ≤ N ≤ a(log(n + 2))³`, some finite aperiodic monoid `M` with `|M| ≤ N` has
   `Q_{1/3}(Prod_{M,n}) ≥ √n 2^{bN^{1/3}}`.

**Formalization Note.** `Q_{1/3}` is invariant under monoid isomorphism, so a maximum over
representatives of the isomorphism classes is bounded above iff every such monoid is, and below
iff some such monoid is (a witness in any universe has an isomorphic copy in the universe `u`).
`log` is natural, `log₂` is `Real.logb 2`, `log^{1/3}(N+2)` is `(log(N+2))^{1/3}`, and all
non-integer powers are real powers. The closing sentence ("Thus throughout this regime …") is
commentary and is not stated. -/
theorem theorem_80 :
    (∃ C : ℝ, 0 < C ∧
      ∀ N n : ℕ, 1 ≤ N → 1 ≤ n →
        ∀ (M : Type u) [Monoid M] [Fintype M] [DecidableEq M], IsAperiodic M →
          Fintype.card M ≤ N →
          (Q13 (prodMap (Finset.univ : Finset M) n) Finset.univ : ℝ≥0∞) ≤
            ENNReal.ofReal (min (n : ℝ) (Real.sqrt n * (2 : ℝ) ^ (C * (N : ℝ) ^ ((1 : ℝ) / 3)) *
              (2 + Real.logb 2 (n + 2)) ^
                (C * (N : ℝ) ^ ((1 : ℝ) / 3) * Real.log (N + 2) ^ ((1 : ℝ) / 3))))) ∧
    (∃ a b : ℝ, 0 < a ∧ 0 < b ∧ ∃ N₀ : ℕ,
      ∀ N n : ℕ, 1 ≤ N → 1 ≤ n → N₀ ≤ N → (N : ℝ) ≤ a * Real.log (n + 2) ^ 3 →
        ∃ (M : Type u) (_ : Monoid M) (_ : Fintype M) (_ : DecidableEq M),
          IsAperiodic M ∧ Fintype.card M ≤ N ∧
          ENNReal.ofReal (Real.sqrt n * (2 : ℝ) ^ (b * (N : ℝ) ^ ((1 : ℝ) / 3))) ≤
            (Q13 (prodMap (Finset.univ : Finset M) n) Finset.univ : ℝ≥0∞)) := by sorry

end MonoidProdQ.Supplement
