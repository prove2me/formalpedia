-- Prove2me | Theorems.Thm_OWFLocalDesc_theorem_4_7
-- name    : OWFLocalDesc.theorem_4_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:44:08.587896+00:00
-- url     : https://prove2.me/theorems/2cd84c86-9775-4617-a18c-59577077124e
-- title:
--   Theorem 4.7 ($k$-wise independent function families, cited from Vadhan)
-- statement:
--   There is a uniform family of functions $F_{n,b,k,\mathrm{seed}}:\{0,1\}^n\to\{0,1\}^b$ such that for all positive integers $n,b,k$ with $k\le 2^n$:
--
--   1. a member is chosen by a seed of exactly $k\max\{n,b\}$ uniformly random bits;
--   2. a member is evaluated deterministically in time polynomial in $n,b,k$;
--   3. for every list of at most $k$ distinct inputs, the outputs are independent and uniform over a uniform seed.
--
--   The independent-concept sampler of Lemma 4.8 is built from this family with output length one.
--
--   **Formalization Note** Clause 3 is stated exactly: for distinct $x_1,\dots,x_j$ with $j\le k$ and every target $(b_1,\dots,b_j)$, $\Pr_{\mathrm{seed}}[F(x_i)=b_i\ \forall i]=2^{-jb}$.
--
--   Differences from the source:
--   - encoding: a uniform family evaluated in time polynomial in n, b, k; outputs independent and uniform → one `CookPvsNP.PolyTimeComputable` evaluator on the code of (1^n, 1^b, 1^k, seed, input); every output tuple on j ≤ k distinct inputs has probability exactly 2^{−jb}; reason: unary parameters make the time bound polynomial in the input length; joint uniformity is the paper's 'independent and uniform'
-- source:
--   Myrisiotis, One-Way Functions and Local Descriptions of Random Data, STOC 2027 submission (held manuscript, sha256 d818fa43…4c4e), Theorem 4.7, p.23 (cited from [Vad12, Corollary 3.34 and Remark 3.25])

import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_QuantumPRC_IsPolyFamily
set_option autoImplicit false

namespace OWFLocalDesc

/-- **Theorem 4.7 (Independent function families), cited from [Vad12].** Myrisiotis, *One-Way Functions and Local Descriptions of Random Data*, STOC 2027 submission
(held manuscript, sha256 d818fa43…4c4e),
Theorem 4.7, p.23: "For positive integers n, b, k with k ≤ 2^n, there is a uniform family of k-wise
independent functions from {0,1}^n to {0,1}^b [Vad12, Corollary 3.34 and Remark 3.25]. A uniformly
random member of the family can be chosen with exactly k max{n,b} random bits, and evaluated
deterministically in time polynomial in n, b, k. For every list of at most k distinct inputs, its
outputs are independent and uniform."

**Formalization Note.** `F n b k seed` is the family member with seed `seed ∈ {0,1}^{k·max(n,b)}`.
"Uniform" and the running time are one polynomial-time evaluator on the code of
`(1ⁿ, 1ᵇ, 1ᵏ, seed, input)`. "Independent and uniform" is: for distinct inputs `x₁,…,x_j`
(`j ≤ k`) every tuple of outputs has probability exactly `2^{−jb}` over a uniform seed. -/
theorem theorem_4_7 :
    ∃ F : (n b k : ℕ) → (Fin (k * max n b) → Bool) → (Fin n → Bool) → (Fin b → Bool),
      (∃ g : List Bool → List Bool, CookPvsNP.PolyTimeComputable g ∧
        ∀ (n b k : ℕ), 0 < n → 0 < b → 0 < k → k ≤ 2 ^ n →
          ∀ (seed : Fin (k * max n b) → Bool) (x : Fin n → Bool),
            g (QuantumPRC.tupleCode [QuantumPRC.unary n, QuantumPRC.unary b, QuantumPRC.unary k,
              List.ofFn seed, List.ofFn x]) = List.ofFn (F n b k seed x)) ∧
      ∀ (n b k : ℕ), 0 < n → 0 < b → 0 < k → k ≤ 2 ^ n →
        ∀ (j : ℕ), j ≤ k → ∀ xs : Fin j → (Fin n → Bool), Function.Injective xs →
          ∀ target : Fin j → Fin b → Bool,
            (open Classical in
              ((Finset.univ.filter fun seed : Fin (k * max n b) → Bool =>
                  ∀ i, F n b k seed (xs i) = target i).card : ℝ)) / (2 : ℝ) ^ (k * max n b) =
              1 / (2 : ℝ) ^ (j * b) := by sorry

end OWFLocalDesc
