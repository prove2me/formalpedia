-- Prove2me | Theorems.Thm_MonoidProdQ_Supplement_theorem_22
-- name    : MonoidProdQ.Supplement.theorem_22
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T11:17:01.434381+00:00
-- url     : https://prove2.me/theorems/d7b16dd3-c02b-4786-ac51-3e1cb4672d66
-- title:
--   Theorem 22 — commutative idempotent monoids: $\beta_G(M)\le\lfloor\log_2(|L_G|+1)\rfloor$
-- statement:
--   Let $M$ be a finite commutative idempotent monoid ($a^2=a$ for all $a$), $G\subseteq M$, and $L_G=\{\bigvee H:\emptyset\ne H\subseteq G\}$ its nonempty join-closure. Then:
--
--   1. $$\beta_G(M)\le\bigl\lfloor\log_2(|L_G|+1)\bigr\rfloor;\tag{19}$$
--   2. for every $n\ge1$, $$\mathrm{ADV}^\pm(\mathrm{Prod}_{M,G,n})\le16\sqrt{n\min\{n,\lfloor\log_2(|L_G|+1)\rfloor\}};\tag{20}$$
--   3. $Q_{1/3}(\mathrm{Prod}_{M,G,n})\le C\sqrt{n\min\{n,\lfloor\log_2(|L_G|+1)\rfloor\}}$ for $n\ge1$, with a universal constant $C$.
--
--   For idempotent monoids the breadth is logarithmic in the number of joins the alphabet generates.
--
--   **Formalization Note** $\beta_G(M)$ is the published product breadth (in $\mathbb N\cup\{\infty\}$), so (19) also asserts finiteness.
--
--   Differences from the source:
--
--   - encoding: O(√(n min{n, ⌊log₂(|L_G| + 1)⌋))) → ∃ universal C > 0; reason: an O-bound with a universal constant
--   - encoding: ⌊log₂(|L_G| + 1)⌋ → Nat.log 2 (|L_G| + 1); reason: the floor of the base-2 logarithm of a positive integer
--   - encoding: n ≥ 1 input positions (standing assumption, p.21) → 1 ≤ n as a hypothesis; reason: with no position the platform's query register is empty and Q_{1/3} is the undefined value ⊤
-- source:
--   Lee–Santha, The quantum query complexity of the semigroup product problem, arXiv:2609.39974 (held version, sha256 9eec405d…ffb6), Theorem 22 (Commutative idempotent product), p.35

import Definitions.Def_MonoidProdQ_productBreadth
import Definitions.Def_MonoidProdQ_prodMap
import Definitions.Def_MonoidProdQ_advPm
import Definitions.Def_MonoidProdQ_Q13
import Definitions.Def_MonoidProdQ_Supplement_joinClosure

open scoped ENNReal

universe u

namespace MonoidProdQ.Supplement

/-- Lee–Santha, *The quantum query complexity of the semigroup product problem*,
arXiv:2609.39974 (held version, sha256 9eec405d…ffb6), Theorem 22 (Commutative idempotent
product), p.35: "Let M be finite, commutative, and idempotent. Let G ⊆ M, and let L_G be its
nonempty join-closure. Then β_G(M) ≤ ⌊log₂(|L_G| + 1)⌋. (19) Consequently,
ADV±(Prod_{M,G,n}) ≤ 16√(n min{n, ⌊log₂(|L_G| + 1)⌋}). (20) In particular,
Q_{1/3}(Prod_{M,G,n}) = O(√(n min{n, ⌊log₂(|L_G| + 1)⌋}))." Three conjuncts: Eq. (19) for every
`G`; Eq. (20) for every `G` and `n ≥ 1`; the query bound with one universal `C > 0`.

**Formalization Note.** Idempotent is `∀ a, a * a = a`. `L_G` is `joinClosure G` (products over
nonempty subsets of `G`). `⌊log₂(m)⌋` for the natural number `m = |L_G| + 1 ≥ 1` is `Nat.log 2 m`.
`β_G(M)` is `productBreadth G` in `ℕ∞`; Eq. (19) also asserts that it is finite. `Prod_{M,G,n}`
is `prodMap G n` on all of `Gⁿ`. -/
theorem theorem_22 :
    (∀ (M : Type u) [CommMonoid M] [Fintype M] [DecidableEq M], (∀ a : M, a * a = a) →
      ∀ G : Finset M, productBreadth G ≤ (Nat.log 2 ((joinClosure G).card + 1) : ℕ∞)) ∧
    (∀ (M : Type u) [CommMonoid M] [Fintype M] [DecidableEq M], (∀ a : M, a * a = a) →
      ∀ (G : Finset M) (n : ℕ), 1 ≤ n →
        advPm (prodMap G n) Finset.univ ≤
          ENNReal.ofReal (16 * Real.sqrt (n * (min n (Nat.log 2 ((joinClosure G).card + 1)) : ℕ)))) ∧
    (∃ C : ℝ, 0 < C ∧
      ∀ (M : Type u) [CommMonoid M] [Fintype M] [DecidableEq M], (∀ a : M, a * a = a) →
        ∀ (G : Finset M) (n : ℕ), 1 ≤ n →
          (Q13 (prodMap G n) Finset.univ : ℝ≥0∞) ≤
            ENNReal.ofReal
              (C * Real.sqrt (n * (min n (Nat.log 2 ((joinClosure G).card + 1)) : ℕ)))) := by sorry

end MonoidProdQ.Supplement
