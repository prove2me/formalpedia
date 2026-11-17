-- Prove2me | Theorems.Thm_LinSSWorst_Supplement_theorem_5_3
-- name    : LinSSWorst.Supplement.theorem_5_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T12:49:05.835208+00:00
-- url     : https://prove2.me/theorems/a807b279-4016-429d-a7c3-5cc110b08be5
-- title:
--   Theorem 5.3 (Layerwise upslice theorem, = Theorem 1.2) — linear schemes for $(k,n)$-upslices with total share length $\frac1{p_{k,q,t}}[\binom{n-q}{k-t}+\sum_{j=t}^q\binom qj]\,O(n^2\log(n+1))$
-- statement:
--   There is an absolute constant $C>0$ such that the following holds. Let $F$ be a finite field and let $n\ge1$, $1\le k\le n$, $0\le q\le n-1$ and $\max\{0,k-(n-q)\}\le t\le\min\{k,q\}$, and put
--   $$p_{k,q,t}=\binom qt\binom{n-q}{k-t}\Big/\binom nk.$$
--   Then every $(k,n)$-upslice has a linear secret-sharing scheme over $F$ with total share length at most
--   $$\frac1{p_{k,q,t}}\left[\binom{n-q}{k-t}+\sum_{j=t}^q\binom qj\right]C\,n^2\log(n+1).$$
--   Moreover, when $t=\lceil kq/n\rceil$, every $(k,n)$-upslice has such a scheme with total share length at most $\left[\binom{n-q}{k-t}+\sum_{j=t}^q\binom qj\right]C\,n^2\log(n+1)$.
--
--   Optimizing $q$ and $t$ gives the upslice exponents of Corollaries 1.3 and 1.4 and the bottom part of the decomposition behind Theorems 1.5 and 1.6.
--
--   **Formalization Note** Linear schemes are those of Definition A.3 and total share length is $\sum_i\ell_i$; the logarithm is natural.
--
--   Differences from the source:
--   - reading: O(n² log(n + 1)) → C · n² · log(n + 1) with one C > 0 chosen before F, n, k, q, t and the upslice, for both clauses; reason: the strongest reading; the proof's constant is absolute (m ≤ ⌈log₂(q + 1)⌉ for every F)
--   - encoding: log(n + 1) → Real.log (n + 1); reason: another base changes only C
--   - encoding: max{0, k − (n − q)} ≤ t; t = ⌈kq/n⌉ → k − (n − q) ≤ t in ℕ; t = Nat.ceil (kq/n); reason: truncated subtraction is max{0, ·}; kq/n ≥ 0
-- source:
--   Nir, Resolving the Worst-Case Complexity of Linear Secret Sharing, preprint (STOC 2027 submission, version of 2026-11-02, sha256 5521cfdb…), Theorem 5.3, p.17 (eq. (6)); parameters of Lemma 5.1, p.16; Theorem 1.2, p.4

import Mathlib
import Definitions.Def_LinSSWorst_Realizes
import Definitions.Def_LinSSWorst_Supplement_IsUpslice

namespace LinSSWorst.Supplement

/-- **Theorem 5.3 (Layerwise upslice theorem)** (= Theorem 1.2, p.4), p.17, from O. Nir, *Resolving the
Worst-Case Complexity of Linear Secret Sharing*, preprint (STOC 2027 submission, version of 2026-11-02,
sha256 5521cfdb…). There is an absolute constant `C > 0` such that for every finite field `F` and all
`n, k, q, t` as in Lemma 5.1 (`n ≥ 1`, `1 ≤ k ≤ n`, `0 ≤ q ≤ n − 1`, `max{0, k − (n − q)} ≤ t ≤ min{k, q}`),
every `(k, n)`-upslice has a linear secret-sharing scheme over `F` with total share length at most
`(1/p_{k,q,t}) · (binom(n − q, k − t) + Σ_{j=t}^{q} binom(q, j)) · C n² log(n + 1)`, where
`p_{k,q,t} = binom(q, t) binom(n − q, k − t) / binom(n, k)`; and, when `t = ⌈kq/n⌉`, it has one with total
share length at most `(binom(n − q, k − t) + Σ_{j=t}^{q} binom(q, j)) · C n² log(n + 1)`.

**Formalization Note.** `O(n² log(n + 1))` is read as `C n² log(n + 1)` with one constant `C` chosen before
the field, the parameters and the upslice (the strongest reading; the proof's constant is absolute). The
logarithm is natural (`Real.log`); another base changes only `C`. Linear schemes are those of
Definition A.3 (`F × (Fin ℓr → F) →ₗ[F] Π i, Fin (ℓ i) → F`), and the total share length is `Σ_i ℓ_i`.
`max{0, k − (n − q)} ≤ t` is `k - (n - q) ≤ t` with truncated subtraction. `⌈kq/n⌉` is `Nat.ceil` of the
nonnegative real `kq/n`. `p_{k,q,t} > 0` under the hypotheses. -/
theorem theorem_5_3 :
    ∃ C : ℝ, 0 < C ∧
      ∀ (F : Type*) [Field F] [Fintype F] (n k q t : ℕ), 1 ≤ n → 1 ≤ k → k ≤ n → q ≤ n - 1 →
        k - (n - q) ≤ t → t ≤ k → t ≤ q →
        ∀ fk : (Fin n → Bool) → Bool, IsUpslice fk k →
          (∃ (ℓr : ℕ) (ℓ : Fin n → ℕ)
              (scheme : (F × (Fin ℓr → F)) →ₗ[F] ((i : Fin n) → Fin (ℓ i) → F)),
              Realizes fk scheme ∧
                ((∑ i, ℓ i : ℕ) : ℝ) ≤
                  (1 / (((q.choose t * (n - q).choose (k - t) : ℕ) : ℝ) / (n.choose k : ℝ))) *
                    (((n - q).choose (k - t) : ℝ) + ∑ j ∈ Finset.Icc t q, (q.choose j : ℝ)) *
                    (C * (n : ℝ) ^ 2 * Real.log ((n : ℝ) + 1))) ∧
          (t = ⌈((k * q : ℕ) : ℝ) / (n : ℝ)⌉₊ →
            ∃ (ℓr : ℕ) (ℓ : Fin n → ℕ)
              (scheme : (F × (Fin ℓr → F)) →ₗ[F] ((i : Fin n) → Fin (ℓ i) → F)),
              Realizes fk scheme ∧
                ((∑ i, ℓ i : ℕ) : ℝ) ≤
                  (((n - q).choose (k - t) : ℝ) + ∑ j ∈ Finset.Icc t q, (q.choose j : ℝ)) *
                    (C * (n : ℝ) ^ 2 * Real.log ((n : ℝ) + 1))) := by sorry

end LinSSWorst.Supplement
