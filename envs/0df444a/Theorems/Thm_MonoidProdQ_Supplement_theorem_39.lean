-- Prove2me | Theorems.Thm_MonoidProdQ_Supplement_theorem_39
-- name    : MonoidProdQ.Supplement.theorem_39
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T11:21:32.346224+00:00
-- url     : https://prove2.me/theorems/6c7d5411-1c32-4df4-b1cd-b7d37fcfecf9
-- title:
--   Theorem 39 — ordered products with a linear exponent: $Q_{1/3}\le\min\{n,(C\beta)^\beta\sqrt n(1+\lceil\log_2(n+2)\rceil)^{5\beta/2}\}$
-- statement:
--   Let $M$ be a monoid with a stable partial order ($a\le b\Rightarrow cad\le cbd$) in which $1$ is the minimum, let $G\subseteq M$ be finite, and let $\beta=\beta_G(M)<\infty$.
--
--   1. If $\beta=0$, the product of every word over $G$ is $1$, and $Q_{1/3}(\mathrm{Prod}_{M,G,n})=0$ for $n\ge1$.
--   2. There is an absolute constant $C$ such that, if $\beta\ge1$, then for every $n\ge1$, writing
--   $$B=\min\Bigl\{n,\ (C\beta)^\beta\sqrt n\,\bigl(1+\lceil\log_2(n+2)\rceil\bigr)^{5\beta/2}\Bigr\},$$
--   we have $Q_{1/3}(\mathrm{Prod}_{M,G,n})\le B$, and some quantum algorithm making at most $B$ queries outputs, with probability at least $9/10$ on every input $x$, a product-preserving subword of $x$ with at most $\beta$ positions.
--
--   This generalizes Dürr–Høyer maximum finding to noncommutative products under an order compatible with multiplication.
--
--   **Formalization Note** $M$ may be infinite; only $G$ is finite. The algorithm is the platform's quantum query algorithm with the standard oracle (as in the published $Q_{1/3}$), with an output map to records; the success probability is the total output probability of the good records.
--
--   Differences from the source:
--
--   - encoding: β = β_G(M) < ∞ → β_G(M) = β for a natural number β; reason: same condition
--   - encoding: an algorithm achieving this bound → ∃ T ≤ B and a T-query algorithm with an output map to records; reason: the platform's query model, as in the published Q_{1/3}
--   - encoding: absolute constant C → ∃ C > 0 chosen before M, G, β, n; reason: the stated absoluteness
--   - encoding: n ≥ 1 input positions (standing assumption, p.21) → 1 ≤ n as a hypothesis; reason: with no position the platform's query register is empty and Q_{1/3} is the undefined value ⊤
-- source:
--   Lee–Santha, The quantum query complexity of the semigroup product problem, arXiv:2609.39974 (held version, sha256 9eec405d…ffb6), Theorem 39 (Ordered products: a linear exponent), p.54

import Definitions.Def_MonoidProdQ_productBreadth
import Definitions.Def_MonoidProdQ_prodMap
import Definitions.Def_MonoidProdQ_Q13
import Definitions.Def_MonoidProdQ_Supplement_IsPreservingRecord

open scoped ENNReal
open QAlgorithms

universe u

namespace MonoidProdQ.Supplement

/-- Lee–Santha, *The quantum query complexity of the semigroup product problem*,
arXiv:2609.39974 (held version, sha256 9eec405d…ffb6), Theorem 39 (Ordered products: a linear
exponent), p.54: "Let M be a monoid with a known stable partial order in which the identity is
the minimum element. Let G ⊆ M be finite, and put β = β_G(M) < ∞. If β = 0, the product is the
identity and no queries are needed. Suppose β ≥ 1. There is an absolute constant C such that,
for every integer n ≥ 1, Q_{1/3}(Prod_{M,G,n}) ≤ min{n, (Cβ)^β √n (1 + ⌈log₂(n + 2)⌉)^{5β/2}}.
Moreover, there is an algorithm achieving this bound which also returns a product-preserving
subword of at most β positions, with probability at least 9/10." Two conjuncts:

1. `β = 0`: the product is `1` on every input, and `Q_{1/3}(Prod_{M,G,n}) = 0` for `n ≥ 1`;
2. one absolute `C > 0` (chosen before `M`, `G`, `β`, `n`) such that for `1 ≤ β < ∞` and
   `n ≥ 1`, with `B = min{n, (Cβ)^β √n (1 + ⌈log₂(n + 2)⌉)^{5β/2}}`:
   `Q_{1/3}(Prod_{M,G,n}) ≤ B`, and there is a `T`-query algorithm with `T ≤ B` and an output
   map to records such that on every input `x` the output is a product-preserving subword of
   `x` with at most `β` positions (`IsPreservingRecord`) with probability at least `9/10`.

**Formalization Note.** Definition 1 (p.7): the order is stable (`a ≤ b ⟹ cad ≤ cbd`) and `1` is
its minimum; `M` may be infinite, only `G` is finite. `β < ∞` is written `β_G(M) = β` for a
natural number `β`. `Prod_{M,G,n}` is `prodMap G n` on all of `Gⁿ`; the algorithm is the
platform's `QueryAlg` with the one-hot standard oracle, as in the published `Q13`, with a finite
workspace `Fin m`; the probability of the event is the sum of the output probabilities of the
records in it. `log₂` is `Real.logb 2`, `⌈·⌉` the integer ceiling, and the exponent `5β/2` is a
real power. -/
theorem theorem_39 :
    (∀ (M : Type u) [Monoid M] [PartialOrder M] [DecidableEq M],
      (∀ a b c d : M, a ≤ b → c * a * d ≤ c * b * d) → (∀ a : M, 1 ≤ a) →
      ∀ G : Finset M, productBreadth G = 0 →
        (∀ (n : ℕ) (x : Fin n → G), prodMap G n x = 1) ∧
        ∀ n : ℕ, 1 ≤ n → Q13 (prodMap G n) Finset.univ = 0) ∧
    (∃ C : ℝ, 0 < C ∧
      ∀ (M : Type u) [Monoid M] [PartialOrder M] [DecidableEq M],
        (∀ a b c d : M, a ≤ b → c * a * d ≤ c * b * d) → (∀ a : M, 1 ≤ a) →
        ∀ (G : Finset M) (β : ℕ), productBreadth G = β → 1 ≤ β → ∀ n : ℕ, 1 ≤ n →
          (Q13 (prodMap G n) Finset.univ : ℝ≥0∞) ≤
              ENNReal.ofReal (min (n : ℝ) ((C * β) ^ β * Real.sqrt n *
                (1 + (⌈Real.logb 2 (n + 2)⌉ : ℝ)) ^ ((5 * β : ℝ) / 2))) ∧
            ∃ (T m : ℕ) (A : QueryAlg (Fin n) (G → ZMod 2) (Fin m) T)
              (out : (Fin n × (G → ZMod 2)) × Fin m → (Fin n → Option G)),
              (T : ℝ) ≤ min (n : ℝ) ((C * β) ^ β * Real.sqrt n *
                (1 + (⌈Real.logb 2 (n + 2)⌉ : ℝ)) ^ ((5 * β : ℝ) / 2)) ∧
              ∀ x : Fin n → G, (9 / 10 : ℝ) ≤
                ∑ ρ ∈ Finset.univ.filter (fun ρ => IsPreservingRecord x β ρ),
                  A.outputProb (xorOracle fun i => oneHot (x i)) out ρ) := by sorry

end MonoidProdQ.Supplement
