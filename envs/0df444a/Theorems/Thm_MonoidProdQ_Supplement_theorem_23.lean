-- Prove2me | Theorems.Thm_MonoidProdQ_Supplement_theorem_23
-- name    : MonoidProdQ.Supplement.theorem_23
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T11:17:52.100212+00:00
-- url     : https://prove2.me/theorems/0da21b0e-dc48-43f0-a557-4b74ab97619c
-- title:
--   Theorem 23 — index two: $\beta_G(M)\le5\log_2|M|$ when $x^3=x^2$, strictly for $|M|\ge2$
-- statement:
--   Let $M$ be a finite commutative monoid with $x^3=x^2$ for every $x\in M$, and let $G\subseteq M$. Then:
--
--   1. $\beta_G(M)$ is finite and $$\beta_G(M)\le5\log_2|M|,\tag{21}$$ with strict inequality $\beta_G(M)<5\log_2|M|$ when $|M|\ge2$;
--   2. for every $n\ge1$, $$\mathrm{ADV}^\pm(\mathrm{Prod}_{M,G,n})\le16\sqrt{n\min\{n,5\log_2|M|\}};\tag{22}$$
--   3. $Q_{1/3}(\mathrm{Prod}_{M,G,n})\le C\sqrt{n\min\{n,\log(|M|+1)\}}$ for $n\ge1$, with a universal constant $C$.
--
--   **Formalization Note** $\log$ is natural and $\log_2$ base two (Conventions, p.23); the minima are taken in $\mathbb R$.
--
--   Differences from the source:
--
--   - encoding: β_G(M) ≤ 5 log₂|M| with β_G(M) ∈ ℕ ∪ {∞} → β_G(M) ≠ ⊤ and its natural value compared with the real bound; reason: same statement: the bound forces finiteness
--   - encoding: O(√(n min{n, log(|M| + 1)})) → ∃ universal C > 0; reason: an O-bound with a universal constant
--   - encoding: n ≥ 1 input positions (standing assumption, p.21) → 1 ≤ n as a hypothesis; reason: with no position the platform's query register is empty and Q_{1/3} is the undefined value ⊤
-- source:
--   Lee–Santha, The quantum query complexity of the semigroup product problem, arXiv:2609.39974 (held version, sha256 9eec405d…ffb6), Theorem 23 (Index two), p.36

import Definitions.Def_MonoidProdQ_productBreadth
import Definitions.Def_MonoidProdQ_prodMap
import Definitions.Def_MonoidProdQ_advPm
import Definitions.Def_MonoidProdQ_Q13

open scoped ENNReal

universe u

namespace MonoidProdQ.Supplement

/-- Lee–Santha, *The quantum query complexity of the semigroup product problem*,
arXiv:2609.39974 (held version, sha256 9eec405d…ffb6), Theorem 23 (Index two), p.36: "Let M be a
finite commutative monoid satisfying x³ = x² for every x ∈ M. Let G ⊆ M be the allowed alphabet.
Then β_G(M) ≤ 5 log₂|M|, (21) and, when |M| ≥ 2, the strict inequality β_G(M) < 5 log₂|M| holds.
Consequently ADV±(Prod_{M,G,n}) ≤ 16√(n min{n, 5 log₂|M|}). (22) In particular,
Q_{1/3}(Prod_{M,G,n}) = O(√(n min{n, log(|M| + 1)}))." Three conjuncts: `β_G(M)` is finite and
satisfies Eq. (21), strictly when `|M| ≥ 2`; Eq. (22) for `n ≥ 1`; the query bound with one
universal `C > 0`.

**Formalization Note.** `log₂` is `Real.logb 2` and the bare `log` natural (Conventions, p.23).
`β_G(M) = productBreadth G` is in `ℕ∞`; it is compared with the real bound after `toNat`, its
finiteness being asserted first. The minima in Eqs. (22) and the query bound are taken in `ℝ`.
`Prod_{M,G,n}` is `prodMap G n` on all of `Gⁿ`. -/
theorem theorem_23 :
    (∀ (M : Type u) [CommMonoid M] [Fintype M] [DecidableEq M], (∀ x : M, x ^ 3 = x ^ 2) →
      ∀ G : Finset M, productBreadth G ≠ ⊤ ∧
        ((productBreadth G).toNat : ℝ) ≤ 5 * Real.logb 2 (Fintype.card M) ∧
        (2 ≤ Fintype.card M → ((productBreadth G).toNat : ℝ) < 5 * Real.logb 2 (Fintype.card M))) ∧
    (∀ (M : Type u) [CommMonoid M] [Fintype M] [DecidableEq M], (∀ x : M, x ^ 3 = x ^ 2) →
      ∀ (G : Finset M) (n : ℕ), 1 ≤ n →
        advPm (prodMap G n) Finset.univ ≤
          ENNReal.ofReal (16 * Real.sqrt (n * min (n : ℝ) (5 * Real.logb 2 (Fintype.card M))))) ∧
    (∃ C : ℝ, 0 < C ∧
      ∀ (M : Type u) [CommMonoid M] [Fintype M] [DecidableEq M], (∀ x : M, x ^ 3 = x ^ 2) →
        ∀ (G : Finset M) (n : ℕ), 1 ≤ n →
          (Q13 (prodMap G n) Finset.univ : ℝ≥0∞) ≤
            ENNReal.ofReal
              (C * Real.sqrt (n * min (n : ℝ) (Real.log (Fintype.card M + 1))))) := by sorry

end MonoidProdQ.Supplement
