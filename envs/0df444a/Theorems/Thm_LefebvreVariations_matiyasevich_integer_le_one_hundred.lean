-- Prove2me | Theorems.Thm_LefebvreVariations_matiyasevich_integer_le_one_hundred
-- name    : LefebvreVariations.matiyasevich_integer_le_one_hundred
-- status  : Open
-- author  : @Secousses
-- created : 2026-11-26T21:20:01.879413+00:00
-- url     : https://prove2.me/theorems/2c2b54bc-04e8-582b-99cc-fb5f4d8f1273
-- title:
--   Lefebvre's variations, No. 192 — on a theme by Matiyasevich: Matiyasevich's integer inequality holds for n at most one hundred
-- statement:
--   Write $E(m)=2^m\,m!$, $d(n)=\sum_{k=1}^{n-1}(-1)^{k+1}\lfloor E(n-1)/k\rfloor$, $l(n)=\lfloor\log_2\operatorname{lcm}(1,\dots,n)\rfloor$, $f_0(n)=\lfloor E(n)/2\rfloor$ and $f_3(n)=\prod_{j=2}^{n}(2j+3)$. For every integer $1\le n\le100$,
--   $$
--   \pi(n)^2\bigl(d(n)\,l(n)-f_0(n)\bigr)\ <\ f_3(n),
--   $$
--   where $\pi(n)$ is the number of primes $\le n$.
--
--   The parent asserts this for all $n\ge1$, an arithmetic (integer-only) equivalent of the Riemann hypothesis. For $n\le100$ both sides are explicit integers, so the statement is a finite exact computation.
--
--   **Formalization Note** The statement is that of `BroughanRH.matiyasevichInteger` verbatim, with the added hypothesis `n ≤ 100`. All divisions are natural-number floor divisions and `Nat.log2` is the floor of the binary logarithm, exactly as in the parent; for $n=1$ the left side is $0<1$.
--
--   **Why this is a variation.** Variation on the open platform theorem BroughanRH.matiyasevichInteger (an integer-only equivalent of the Riemann hypothesis): the parent's own inequality for n <= 100, where each side is an explicit integer; a prover can discharge it by kernel computation.
--
--   **Attribution.** This statement belongs to *Lefebvre's variations*, a series proposed by Erwan Lefebvre: each variation plays an open problem of the platform at its first non-trivial size, so that it can be settled and then reused to attack the open problem itself.
-- source:
--   Statement and name as on the platform (BroughanRH.matiyasevichInteger; the underlying Matiyasevich integer criterion for the Riemann hypothesis, see K. Broughan, Equivalents of the Riemann Hypothesis, Cambridge Univ. Press, 2017; exact reference cited from memory, not confirmed by web search). Truth check: evaluated in exact integer arithmetic in Python, transcribing the Lean definitions literally (floor division, bit_length - 1 for Nat.log2, sympy primepi), for every n from 1 to 199: the inequality holds each time.

import Mathlib

set_option autoImplicit false

namespace LefebvreVariations

theorem matiyasevich_integer_le_one_hundred :
    let evenFact (m : ℕ) := 2^m * m.factorial
    let d (n : ℕ) : ℤ := ∑ k ∈ Finset.Ico 1 n,
      (-1 : ℤ)^(k+1) * ((evenFact (n-1) / k : ℕ) : ℤ)
    let l (n : ℕ) := Nat.log2 ((Finset.Icc 1 n).lcm id)
    let f₀ (n : ℕ) := evenFact n / 2
    let f₃ (n : ℕ) : ℕ := ∏ j ∈ Finset.Icc 2 n, (2*j+3)
    ∀ n : ℕ, 1 ≤ n → n ≤ 100 → (Nat.primeCounting n : ℤ)^2 *
      (d n * (l n : ℤ) - (f₀ n : ℤ)) < (f₃ n : ℤ) := by
  sorry

end LefebvreVariations
