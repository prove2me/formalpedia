-- Prove2me | Theorems.Thm_MonoidProdQ_Supplement_theorem_27
-- name    : MonoidProdQ.Supplement.theorem_27
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T11:19:02.893815+00:00
-- url     : https://prove2.me/theorems/f08616ad-d7b3-4dd6-b6a3-35febfa2783a
-- title:
--   Theorem 27 — capped counters: $\beta(M_{k,r})=kr$ and $Q_{1/3}(\mathrm{Prod}_{M_{k,r},n})=\Theta(\sqrt{n\min\{n,kr\}})$
-- statement:
--   For integers $k,r\ge1$ let $M_{k,r}=C_{k+1}^r$ be the capped counter ($a\oplus b=\min\{a+b,k\}$ in each coordinate). Then:
--
--   1. $\beta_{M_{k,r}}(M_{k,r})=kr$;
--   2. for every $n\ge0$, among words of length $n$ over $M_{k,r}$ the largest length of a shortest product-preserving subword is $\min\{n,kr\}$:
--   $$\sup_{|w|=n}\ \min\{|u|:\ u\preceq w,\ [u]=[w]\}=\min\{n,kr\};$$
--   3. there are universal constants $c,C>0$ with
--   $$c\sqrt{n\min\{n,kr\}}\le Q_{1/3}(\mathrm{Prod}_{M_{k,r},n})\le C\sqrt{n\min\{n,kr\}}\qquad(k,r,n\ge1).\tag{30}$$
--
--   Since $|M_{k,r}|=(k+1)^r$, this shows the dependence on $k$ and $\log|M|$ in Theorem 25 is optimal up to lower-order factors.
--
--   **Formalization Note** Words are lists, $u\preceq w$ is the scattered-subword relation and $[w]$ the product, as in the published product breadth; the supremum and infimum in clause 2 are in $\mathbb N\cup\{\infty\}$.
--
--   Differences from the source:
--
--   - encoding: Θ(√(n min{n, kr})) → universal c, C > 0 chosen before k, r, n; reason: the paper derives (30) from Theorem 18, whose constants are universal
--   - encoding: n ≥ 1 input positions (standing assumption, p.21) → 1 ≤ n as a hypothesis; reason: with no position the platform's query register is empty and Q_{1/3} is the undefined value ⊤
-- source:
--   Lee–Santha, The quantum query complexity of the semigroup product problem, arXiv:2609.39974 (held version, sha256 9eec405d…ffb6), Theorem 27 (Capped-counter products), p.39

import Definitions.Def_MonoidProdQ_productBreadth
import Definitions.Def_MonoidProdQ_prodMap
import Definitions.Def_MonoidProdQ_Q13
import Definitions.Def_MonoidProdQ_Supplement_CappedCounter

open scoped ENNReal

namespace MonoidProdQ.Supplement

/-- Lee–Santha, *The quantum query complexity of the semigroup product problem*,
arXiv:2609.39974 (held version, sha256 9eec405d…ffb6), Theorem 27 (Capped-counter products),
p.39, for integers `k, r ≥ 1` (§5.5, p.39): "The product-preserving subword parameter is
β_{M_{k,r}}(M_{k,r}) = kr. Among words of length n, the largest length of a shortest preserving
subword is min{n, kr}. Moreover, Q_{1/3}(Prod_{M_{k,r},n}) = Θ(√(n min{n, kr})). (30)" Three
conjuncts:

1. `β_{M_{k,r}}(M_{k,r}) = kr`;
2. for every `n`, `sup_{|w| = n} min{|u| : u ⪯ w, [u] = [w]} = min{n, kr}` over words `w` of
   length `n` over `M_{k,r}`;
3. universal `c, C > 0` with `c√(n·min{n, kr}) ≤ Q_{1/3}(Prod_{M_{k,r},n}) ≤ C√(n·min{n, kr})`
   for all `k, r, n ≥ 1`.

**Formalization Note.** `M_{k,r}` is `CappedCounter k r`. Words are lists, `⪯` is
`List.Sublist` and `[w]` the list product, as in the published `productBreadth`; the supremum
and infimum of clause 2 are in `ℕ∞`. `Prod_{M_{k,r},n}` is `prodMap univ n` on all of `M_{k,r}ⁿ`.
The `Θ` constants are universal: the paper obtains Eq. (30) from Theorem 18, whose constants
are universal. -/
theorem theorem_27 :
    (∀ k r : ℕ, 1 ≤ k → 1 ≤ r →
      productBreadth (Finset.univ : Finset (CappedCounter k r)) = ((k * r : ℕ) : ℕ∞)) ∧
    (∀ k r : ℕ, 1 ≤ k → 1 ≤ r → ∀ n : ℕ,
      (⨆ (w : List (CappedCounter k r)) (_ : w.length = n),
        ⨅ (u : List (CappedCounter k r)) (_ : u.Sublist w ∧ u.prod = w.prod), (u.length : ℕ∞)) =
          ((min n (k * r) : ℕ) : ℕ∞)) ∧
    (∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ k r n : ℕ, 1 ≤ k → 1 ≤ r → 1 ≤ n →
      ENNReal.ofReal (c * Real.sqrt (n * (min n (k * r) : ℕ))) ≤
          (Q13 (prodMap (Finset.univ : Finset (CappedCounter k r)) n) Finset.univ : ℝ≥0∞) ∧
        (Q13 (prodMap (Finset.univ : Finset (CappedCounter k r)) n) Finset.univ : ℝ≥0∞) ≤
          ENNReal.ofReal (C * Real.sqrt (n * (min n (k * r) : ℕ)))) := by sorry

end MonoidProdQ.Supplement
