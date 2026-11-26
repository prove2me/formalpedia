-- Prove2me | Theorems.Thm_LefebvreVariations_perfect_code_binary_le_seven
-- name    : LefebvreVariations.perfect_code_binary_le_seven
-- status  : Open
-- author  : @Secousses
-- created : 2026-11-25T23:45:52.28785+00:00
-- url     : https://prove2.me/theorems/081b1925-6b65-5d3e-9712-803d5fed73f2
-- title:
--   Lefebvre's variations, No. 63 — on a theme by Hamming: a binary perfect one-error-correcting code of length n at most 7 exists iff n is 1, 3 or 7
-- statement:
--   Let $1\le n\le 7$. A binary code of length $n$ with minimum distance at least $3$ and at least $2^n/(n+1)$ words exists if and only if $n\in\{1,3,7\}$, that is, if and only if $n=2^k-1$ for some $k\ge 0$. Precisely: there is a set $C\subseteq\{0,1\}^n$ such that any two distinct words of $C$ differ in at least $3$ positions and
--   $$
--   2^n \;\le\; |C|\,(1+n)
--   $$
--   if and only if $n=2^k-1$ for some $k\in\mathbb{N}$.
--
--   Such a code is a perfect $1$-error-correcting binary code: the Hamming balls of radius $1$ around its words are disjoint and cover $\{0,1\}^n$. For $n\le 7$ they exist exactly for $n=1$ (the code with a single word), $n=3$ (the repetition code $\{000,111\}$) and $n=7$ (the Hamming code with $16$ words). This is the case $q=2$, $n\le 7$ of the open question on the platform, which asks for which alphabet sizes $q$ and lengths $n$ a perfect $1$-error-correcting code over an alphabet with $q$ letters exists, with the conjectured answer $n=(q^k-1)/(q-1)$.
--
--   **Formalization Note** The code is a `Finset (Fin n → Fin q)` with `q = 2`. The distance condition is `∀ x ∈ C, ∀ y ∈ C, x ≠ y → 3 ≤ ∑ i, if x i ≠ y i then 1 else 0` (Hamming distance at least $3$ between distinct words), and the covering condition is `(Finset.univ).card ≤ C.card * (1 + n * (q - 1))`, which is `2^n ≤ |C|(n+1)` for `q = 2`; together with the distance condition (sphere packing) it forces equality. The right-hand side `∃ k : ℕ, n = (q ^ k - 1) / (q - 1)` is `n = 2^k - 1` for `q = 2`; since `n ≥ 1` the value `k = 0` (which gives $n=0$) does not occur. The hypotheses are `1 ≤ n`, `n ≤ 7`, `2 ≤ q` and `q = 2` (the second condition on `q` is redundant); the statement is an equivalence, so both directions are proved.
--
--   **Why this is a variation.** Variation on the open perfect_1_error_correcting_code problem (classification of perfect 1-error-correcting codes). It fixes the alphabet to q = 2 and bounds the length by n ≤ 7, the range containing the repetition and Hamming codes, so it is a small case of the parent with the parent's conclusion kept.
--
--   **Attribution.** This statement belongs to *Lefebvre's variations*, a series proposed by Erwan Lefebvre: each variation plays an open problem of the platform at its first non-trivial size, so that it can be settled and then reused to attack the open problem itself.
-- source:
--   R. W. Hamming, Error detecting and error correcting codes, Bell System Technical Journal 29 (1950), 147-160 (introduces the Hamming codes and the sphere-packing bound; volume and pages cited from memory, not re-checked). The classification of perfect binary 1-error-correcting codes by length n = 2^k - 1 (the necessity direction is the elementary sphere-packing count (n+1) | 2^n) is textbook material, for instance F. J. MacWilliams and N. J. A. Sloane, The Theory of Error-Correcting Codes (North-Holland, 1977), chapter 6 (chapter number cited from memory, not verified). Origin of this statement: the case q = 2, 1 <= n <= 7 of the platform theorem perfect_1_error_correcting_code (Open), whose conclusion it copies verbatim; it is proved by the packing bound |C|(n+1) <= 2^n (so equality forces (n+1) | 2^n) and by explicit codes of lengths 1, 3 and 7 (syndrome codes), checked by kernel evaluation.

import Mathlib

namespace LefebvreVariations

/-- Perfect 1-error-correcting codes (the Hamming-bound classification) in the binary case
`q = 2` and for lengths `n ≤ 7`. A perfect code exists exactly for `n = 1, 3, 7` (repetition
codes of length 1 and 3, and the Hamming code of length 7): in general a perfect code over
`q = 2` forces `(n + 1) ∣ 2^n` by the sphere-packing bound, hence `n + 1` is a power of two.
Statement as in the parent, with `q = 2` and `n ≤ 7` added as hypotheses.
Source: R. W. Hamming, "Error detecting and error correcting codes", Bell System Technical Journal
29 (1950), 147-160 (cited from memory); the binary classification is also in MacWilliams and
Sloane, "The Theory of Error-Correcting Codes", Ch. 6 (cited from memory). -/
theorem perfect_code_binary_le_seven (n : ℕ) (hn : 1 ≤ n) (hn7 : n ≤ 7) (q : ℕ) (hq : 2 ≤ q)
    (hq2 : q = 2) :
    (∃ (C : Finset (Fin n → Fin q)),
      (∀ x ∈ C, ∀ y ∈ C, x ≠ y → 3 ≤ ∑ i, if x i ≠ y i then 1 else 0) ∧
      (Finset.univ (α := Fin n → Fin q)).card ≤ C.card * (1 + n * (q - 1))) ↔
    ∃ k : ℕ, n = (q ^ k - 1) / (q - 1) := by
  sorry

end LefebvreVariations
