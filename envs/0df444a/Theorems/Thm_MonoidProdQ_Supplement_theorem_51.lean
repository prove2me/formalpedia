-- Prove2me | Theorems.Thm_MonoidProdQ_Supplement_theorem_51
-- name    : MonoidProdQ.Supplement.theorem_51
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T11:23:26.870981+00:00
-- url     : https://prove2.me/theorems/b9d4111f-645d-434e-9c1f-d131d0166b5a
-- title:
--   Theorem 51 — Boolean unitriangular products: $\beta=\binom k2$ and $Q_{1/3}=\Theta(\min\{n,k\sqrt n\})$
-- statement:
--   Let $\mathrm{UT}_k(\mathbb B)$ be the monoid of $k\times k$ upper triangular Boolean matrices with unit diagonal. Then:
--
--   1. $\beta(\mathrm{UT}_k(\mathbb B))=\binom k2$ for $k\ge1$;
--   2. for all $k,n\ge1$,
--   $$\sqrt{\tfrac n2\min\{n,\lfloor k^2/4\rfloor\}}\ \le\ \mathrm{ADV}^\pm(\mathrm{Prod}_{\mathrm{UT}_k(\mathbb B),n})\ \le\ 8\sqrt{n\min\{n,\tbinom k2\}};$$
--   3. $Q_{1/3}(\mathrm{Prod}_{\mathrm{UT}_1(\mathbb B),n})=0$;
--   4. there are universal $c,C>0$ such that for $k\ge2$, $n\ge1$,
--   $$c\min\{n,k\sqrt n\}\le Q_{1/3}(\mathrm{Prod}_{\mathrm{UT}_k(\mathbb B),n})\le C\min\{n,k\sqrt n\},$$
--   and the lower bound already holds for a Boolean postprocessing $h$ of the full product on some promise set $D$.
--
--   **Formalization Note** The breadth of the monoid is over its full alphabet. The promise $D$ and the postprocessing $h$ may depend on $k$ and $n$.
--
--   Differences from the source:
--
--   - encoding: Θ(min{n, k√n}) with universal implicit constants → universal c, C > 0 chosen before k and n; reason: the stated universality
--   - reading: the lower bound already holds for a Boolean postprocessing of the full product on a promise → ∃ D, h (depending on k, n) with the same c; reason: a promise is a set of length-n words, so it depends on n
--   - encoding: ⌊k²/4⌋ → k ^ 2 / 4 in ℕ; reason: natural-number division is the floor
--   - encoding: n ≥ 1 input positions (standing assumption, p.21) → 1 ≤ n as a hypothesis; reason: with no position the platform's query register is empty and Q_{1/3} is the undefined value ⊤
-- source:
--   Lee–Santha, The quantum query complexity of the semigroup product problem, arXiv:2609.39974 (held version, sha256 9eec405d…ffb6), Theorem 51 (Boolean unitriangular products), p.67

import Definitions.Def_MonoidProdQ_productBreadth
import Definitions.Def_MonoidProdQ_prodMap
import Definitions.Def_MonoidProdQ_advPm
import Definitions.Def_MonoidProdQ_Q13
import Definitions.Def_MonoidProdQ_Supplement_UTBool

open scoped ENNReal

namespace MonoidProdQ.Supplement

/-- Lee–Santha, *The quantum query complexity of the semigroup product problem*,
arXiv:2609.39974 (held version, sha256 9eec405d…ffb6), Theorem 51 (Boolean unitriangular
products), p.67: "The monoid UT_k(B) has product breadth (k choose 2). For every k, n ≥ 1,
ADV±(Prod_{UT_k(B),n}) ≤ 8√(n min{n, (k choose 2)}), ADV±(Prod_{UT_k(B),n}) ≥
√((n/2) min{n, ⌊k²/4⌋}). Consequently Q_{1/3}(Prod_{UT_k(B),n}) = 0 for k = 1 and
Θ(min{n, k√n}) for k ≥ 2, with universal implicit constants. The lower bound already holds for a
Boolean postprocessing of the full product on a promise." Five conjuncts:

1. `β(UT_k(B)) = (k choose 2)` for `k ≥ 1`;
2. `ADV±(Prod_{UT_k(B),n}) ≤ 8√(n·min{n, (k choose 2)})` for `k, n ≥ 1`;
3. `ADV±(Prod_{UT_k(B),n}) ≥ √((n/2)·min{n, ⌊k²/4⌋})` for `k, n ≥ 1`;
4. `Q_{1/3}(Prod_{UT_1(B),n}) = 0` for `n ≥ 1`;
5. universal `c, C > 0` such that for `k ≥ 2`, `n ≥ 1`:
   `c·min{n, k√n} ≤ Q_{1/3}(Prod_{UT_k(B),n}) ≤ C·min{n, k√n}`, and there are a promise set
   `D ⊆ UT_k(B)ⁿ` and `h : UT_k(B) → Bool` with `c·min{n, k√n} ≤ Q_{1/3}(h ∘ Prod_{UT_k(B),n})`
   on `D`.

**Formalization Note.** `UT_k(B)` is `UTBool k`; "product breadth" of the monoid is the breadth
over the full alphabet, `productBreadth univ`, in `ℕ∞`. `Prod_{UT_k(B),n}` is `prodMap univ n`
(on all of `UT_k(B)ⁿ`, or on the promise `D` in the last clause). `⌊k²/4⌋` is natural-number
division `k ^ 2 / 4`, and the minima of naturals are taken in `ℕ` before casting. The promise
`D` and the postprocessing `h` may depend on `k` and `n` (a promise is a set of length-`n`
words). The same `c` serves the full product and the postprocessed promise problem. -/
theorem theorem_51 :
    (∀ k : ℕ, 1 ≤ k →
      productBreadth (Finset.univ : Finset (UTBool k)) = ((k.choose 2 : ℕ) : ℕ∞)) ∧
    (∀ k n : ℕ, 1 ≤ k → 1 ≤ n →
      advPm (prodMap (Finset.univ : Finset (UTBool k)) n) Finset.univ ≤
        ENNReal.ofReal (8 * Real.sqrt (n * (min n (k.choose 2) : ℕ)))) ∧
    (∀ k n : ℕ, 1 ≤ k → 1 ≤ n →
      ENNReal.ofReal (Real.sqrt ((n / 2 : ℝ) * (min n (k ^ 2 / 4) : ℕ))) ≤
        advPm (prodMap (Finset.univ : Finset (UTBool k)) n) Finset.univ) ∧
    (∀ n : ℕ, 1 ≤ n → Q13 (prodMap (Finset.univ : Finset (UTBool 1)) n) Finset.univ = 0) ∧
    (∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ k n : ℕ, 2 ≤ k → 1 ≤ n →
      ENNReal.ofReal (c * min (n : ℝ) (k * Real.sqrt n)) ≤
          (Q13 (prodMap (Finset.univ : Finset (UTBool k)) n) Finset.univ : ℝ≥0∞) ∧
        (Q13 (prodMap (Finset.univ : Finset (UTBool k)) n) Finset.univ : ℝ≥0∞) ≤
          ENNReal.ofReal (C * min (n : ℝ) (k * Real.sqrt n)) ∧
        ∃ (D : Finset (Fin n → (Finset.univ : Finset (UTBool k)))) (h : UTBool k → Bool),
          ENNReal.ofReal (c * min (n : ℝ) (k * Real.sqrt n)) ≤
            (Q13 (h ∘ prodMap (Finset.univ : Finset (UTBool k)) n) D : ℝ≥0∞)) := by sorry

end MonoidProdQ.Supplement
