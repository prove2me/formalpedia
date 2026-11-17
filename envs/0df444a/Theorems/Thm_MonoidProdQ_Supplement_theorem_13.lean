-- Prove2me | Theorems.Thm_MonoidProdQ_Supplement_theorem_13
-- name    : MonoidProdQ.Supplement.theorem_13
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T11:14:28.453209+00:00
-- url     : https://prove2.me/theorems/4a3f9a03-b80e-45ad-9d5b-8dd9f32dff71
-- title:
--   Theorem 13 — aperiodicity-index lower bound $Q_{1/3}(\mathrm{Prod}_{M,n})=\Omega(\sqrt{n\min\{n,\iota(M)\}})$
-- statement:
--   Let $\iota(M)$ be the aperiodicity index of a finite aperiodic monoid $M$ (the least $k\ge1$ with $a^k=a^{k+1}$ for all $a$). There is a universal constant $c>0$ such that for every nontrivial finite aperiodic monoid $M$:
--
--   1. for every $n\ge1$,
--   $$Q_{1/3}(\mathrm{Prod}_{M,n})\ \ge\ c\sqrt{n\min\{n,\iota(M)\}}\quad\text{and}\quad Q_{1/3}(\mathrm{Prod}_{M,n})\ \ge\ c\min\{n,\sqrt{n\,\iota(M)}\};$$
--   2. there are a two-letter alphabet $G\subseteq M$ and a Boolean postprocessing $h:M\to\{0,1\}$ such that $Q_{1/3}(h\circ\mathrm{Prod}_{M,G,n})\ge c\sqrt{n\min\{n,\iota(M)\}}$ for every $n\ge1$.
--
--   Thus a large aperiodicity index forces a large query complexity, already on two letters and for a one-bit function of the product.
--
--   **Formalization Note** $\mathrm{Prod}_{M,G,n}$ is the published product map over the alphabet $G$ on all of $G^n$; nontrivial means $|M|>1$.
--
--   Differences from the source:
--
--   - reading: Ω(·) with no subscript → one universal c > 0 chosen before M; reason: the proof is a uniform adversary construction
--   - reading: the lower bound holds on a two-letter alphabet and after Boolean postprocessing → ∃ G with |G| = 2 and h : M → Bool, both chosen before n, with the same c for every n ≥ 1; reason: the stronger reading; the proof's G = {1, x} is independent of n, and the parity of the exponent separates all consecutive layers x^{r−1}, x^r (r ≤ ι(M)) at once
--   - encoding: nontrivial → 1 < Fintype.card M; reason: same instances
--   - encoding: n ≥ 1 input positions (standing assumption, p.21) → 1 ≤ n as a hypothesis; reason: with no position the platform's query register is empty and Q_{1/3} is the undefined value ⊤
-- source:
--   Lee–Santha, The quantum query complexity of the semigroup product problem, arXiv:2609.39974 (held version, sha256 9eec405d…ffb6), Theorem 13 (Aperiodicity-index lower bound), p.26

import Definitions.Def_MonoidProdQ_IsAperiodic
import Definitions.Def_MonoidProdQ_prodMap
import Definitions.Def_MonoidProdQ_Q13
import Definitions.Def_MonoidProdQ_Supplement_aperiodicityIndex

open scoped ENNReal

universe u

namespace MonoidProdQ.Supplement

/-- Lee–Santha, *The quantum query complexity of the semigroup product problem*,
arXiv:2609.39974 (held version, sha256 9eec405d…ffb6), Theorem 13 (Aperiodicity-index lower
bound), p.26: "Let M be a nontrivial finite aperiodic monoid. For every n ≥ 1,
Q_{1/3}(Prod_{M,n}) = Ω(√(n min{n, ι(M)})) = Ω(min{n, √(nι(M))}). The lower bound holds on a
two-letter alphabet and after Boolean postprocessing of the product." One constant `c > 0`,
chosen before `M` and `n`, gives both
`c·√(n·min{n, ι(M)}) ≤ Q_{1/3}(Prod_{M,n})` and `c·min{n, √(nι(M))} ≤ Q_{1/3}(Prod_{M,n})` (both
displayed forms) for every `n ≥ 1`, and, for one two-letter alphabet `G ⊆ M` and one
`h : M → Bool` chosen before `n`, `c·√(n·min{n, ι(M)}) ≤ Q_{1/3}(h ∘ Prod_{M,G,n})` for every
`n ≥ 1`.

**Formalization Note.** `ι(M)` is `aperiodicityIndex M`, nontrivial is `1 < |M|`.
`Prod_{M,G,n}` is `prodMap G n` on all of `Gⁿ`. The alphabet and the postprocessing are fixed
before `n` (the stronger reading; the proof's `G = {1, x}` does not depend on `n`, and since
`x⁰, …, x^k` are distinct in an aperiodic monoid the parity of the exponent separates every pair
of consecutive layers at once). The constant is universal (the bound is an explicit adversary
construction with no `M`-dependent constant). -/
theorem theorem_13 :
    ∃ c : ℝ, 0 < c ∧
      ∀ (M : Type u) [Monoid M] [Fintype M] [DecidableEq M], 1 < Fintype.card M →
        IsAperiodic M →
          (∀ n : ℕ, 1 ≤ n →
            ENNReal.ofReal (c * Real.sqrt (n * (min n (aperiodicityIndex M) : ℕ))) ≤
                (Q13 (prodMap (Finset.univ : Finset M) n) Finset.univ : ℝ≥0∞) ∧
            ENNReal.ofReal (c * min (n : ℝ) (Real.sqrt (n * aperiodicityIndex M))) ≤
                (Q13 (prodMap (Finset.univ : Finset M) n) Finset.univ : ℝ≥0∞)) ∧
          ∃ G : Finset M, G.card = 2 ∧ ∃ h : M → Bool, ∀ n : ℕ, 1 ≤ n →
            ENNReal.ofReal (c * Real.sqrt (n * (min n (aperiodicityIndex M) : ℕ))) ≤
              (Q13 (h ∘ prodMap G n) Finset.univ : ℝ≥0∞) := by sorry

end MonoidProdQ.Supplement
