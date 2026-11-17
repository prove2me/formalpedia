-- Prove2me | Theorems.Thm_MonoidProdQ_Supplement_theorem_46
-- name    : MonoidProdQ.Supplement.theorem_46
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T11:22:51.74622+00:00
-- url     : https://prove2.me/theorems/7c4e9eb8-7232-4997-b06e-c5ce80a9ef70
-- title:
--   Theorem 46 — ordered products with a logarithmic exponent (Result 2)
-- statement:
--   Let $M$ be a monoid with a stable partial order in which $1$ is the minimum, $G\subseteq M$ finite, and $\beta=\beta_G(M)$ with $1\le\beta<\infty$. There is an absolute constant $C$, independent of $M$, $G$ and $\beta$, such that for every $n\ge1$, writing
--   $$B=\min\Bigl\{n,\ \sqrt{n+1}\,\bigl(C(\beta+2)\log(n+2)\bigr)^{C\log(\beta+2)}\Bigr\},\tag{57}$$
--
--   1. $Q_{1/3}(\mathrm{Prod}_{M,G,n})\le B$;
--   2. some quantum algorithm making at most $B$ queries outputs, with probability at least $9/10$ on every input $x$, a product-preserving subword of $x$ with at most $\beta$ positions, and every record it outputs with positive probability agrees with the input.
--
--   For fixed breadth this is $\sqrt n$ times a polylogarithmic factor whose degree grows only logarithmically in $\beta$.
--
--   **Formalization Note** $M$ may be infinite; only $G$ is finite. $\log$ is natural. "On every branch" is read as every measurement outcome of positive probability.
--
--   Differences from the source:
--
--   - encoding: 1 ≤ β < ∞ → β_G(M) = β for a natural number β ≥ 1; reason: same condition
--   - encoding: an algorithm achieving this bound → ∃ T ≤ B and a T-query algorithm with an output map to records; reason: the platform's query model, as in the published Q_{1/3}
--   - encoding: its recorded letters agree with the input on every branch → every record output with positive probability on x agrees with x; reason: a branch of a quantum algorithm is a measurement outcome of positive probability
--   - encoding: n ≥ 1 input positions (standing assumption, p.21) → 1 ≤ n as a hypothesis; reason: with no position the platform's query register is empty and Q_{1/3} is the undefined value ⊤
-- source:
--   Lee–Santha, The quantum query complexity of the semigroup product problem, arXiv:2609.39974 (held version, sha256 9eec405d…ffb6), Theorem 46 (Ordered products: a logarithmic exponent), p.63

import Definitions.Def_MonoidProdQ_productBreadth
import Definitions.Def_MonoidProdQ_prodMap
import Definitions.Def_MonoidProdQ_Q13
import Definitions.Def_MonoidProdQ_Supplement_IsPreservingRecord
import Definitions.Def_MonoidProdQ_Supplement_RecordAgrees

open scoped ENNReal
open QAlgorithms

universe u

namespace MonoidProdQ.Supplement

/-- Lee–Santha, *The quantum query complexity of the semigroup product problem*,
arXiv:2609.39974 (held version, sha256 9eec405d…ffb6), Theorem 46 (Ordered products: a
logarithmic exponent), p.63 (Result 2, p.8): "Let M be a monoid with a known stable partial order
in which the identity is the minimum element. Let G ⊆ M be finite, and put β = β_G(M), where
1 ≤ β < ∞. For an absolute constant C and every n ≥ 1,
Q_{1/3}(Prod_{M,G,n}) ≤ min{n, √(n + 1) (C(β + 2) log(n + 2))^{C log(β+2)}}. (57) Moreover, there
is an algorithm achieving this bound which also returns a product-preserving subword of at most
β positions, with probability at least 9/10. Its recorded letters agree with the input on every
branch. The constant is independent of M, G, and β." One absolute `C > 0`, chosen before `M`,
`G`, `β` and `n`, such that, with `B` the right side of Eq. (57):

1. `Q_{1/3}(Prod_{M,G,n}) ≤ B`;
2. there is a `T`-query algorithm with `T ≤ B` and an output map to records such that on every
   input `x` the output is a product-preserving subword of `x` with at most `β` positions
   (`IsPreservingRecord`) with probability at least `9/10`, and every record it outputs with
   positive probability on `x` agrees with `x` (`RecordAgrees`).

**Formalization Note.** Definition 1 (p.7): the order is stable (`a ≤ b ⟹ cad ≤ cbd`) and `1` is
its minimum; `M` may be infinite, only `G` is finite. `1 ≤ β < ∞` is `β_G(M) = β` for a natural
number `β ≥ 1`. `log` is natural (Conventions, p.23) and both powers are real powers.
`Prod_{M,G,n}` is `prodMap G n` on all of `Gⁿ`; the algorithm is the platform's `QueryAlg` with
the one-hot standard oracle, as in the published `Q13`. "On every branch" is read as every
measurement outcome of positive probability. -/
theorem theorem_46 :
    ∃ C : ℝ, 0 < C ∧
      ∀ (M : Type u) [Monoid M] [PartialOrder M] [DecidableEq M],
        (∀ a b c d : M, a ≤ b → c * a * d ≤ c * b * d) → (∀ a : M, 1 ≤ a) →
        ∀ (G : Finset M) (β : ℕ), productBreadth G = β → 1 ≤ β → ∀ n : ℕ, 1 ≤ n →
          (Q13 (prodMap G n) Finset.univ : ℝ≥0∞) ≤
              ENNReal.ofReal (min (n : ℝ) (Real.sqrt (n + 1) *
                (C * (β + 2) * Real.log (n + 2)) ^ (C * Real.log (β + 2)))) ∧
            ∃ (T m : ℕ) (A : QueryAlg (Fin n) (G → ZMod 2) (Fin m) T)
              (out : (Fin n × (G → ZMod 2)) × Fin m → (Fin n → Option G)),
              (T : ℝ) ≤ min (n : ℝ) (Real.sqrt (n + 1) *
                (C * (β + 2) * Real.log (n + 2)) ^ (C * Real.log (β + 2))) ∧
              (∀ x : Fin n → G, (9 / 10 : ℝ) ≤
                ∑ ρ ∈ Finset.univ.filter (fun ρ => IsPreservingRecord x β ρ),
                  A.outputProb (xorOracle fun i => oneHot (x i)) out ρ) ∧
              ∀ (x : Fin n → G) (ρ : Fin n → Option G),
                0 < A.outputProb (xorOracle fun i => oneHot (x i)) out ρ → RecordAgrees x ρ := by sorry

end MonoidProdQ.Supplement
