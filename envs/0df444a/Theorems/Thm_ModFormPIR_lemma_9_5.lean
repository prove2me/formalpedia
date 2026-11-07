-- Prove2me | Theorems.Thm_ModFormPIR_lemma_9_5
-- name    : ModFormPIR.lemma_9_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:02:18.997293+00:00
-- url     : https://prove2.me/theorems/b8587767-c0ab-4a4d-9420-2f2114fe75ac
-- title:
--   Lemma 9.5, p.35 — primes just above a power of two, in a residue class
-- statement:
--   Fix a prime $q$. There is a randomized algorithm that takes a positive integer $M$ and a sufficiently large integer $n$, and constructs an integer $B$ and a prime $p\equiv1\pmod q$ such that
--   $$p>M,\quad p\ge n^4,\quad 2^B<p\le2^B\Big(1+\frac1{4n}\Big),\quad B=O(\log M+\log^3n).$$
--   This algorithm runs in expected time $\mathrm{poly}(B)$.
--
--   The closeness of $p$ to a power of two is what makes the storage overhead at most one bit: $n/B$ elements of $\mathbb F_p$ fit $n+1$ bits through the dictionary.
--
--   **Formalization Note** Las Vegas on the machine. Output: $B$ in cell $-1$, the bits of $p$ from cell $-2$ downwards.
--
--   Differences from the source:
--   - reading: "randomized algorithm", "expected time poly(B)" → Las Vegas program: every accepting run outputs valid (B, p), and the accept time is measurable with expectation ≤ C·(log₂ M + (log₂ n + 1)³ + 1)^e; reason: the algorithm tests primality; the output constraints force B ≥ max(log₂ M, 4 log₂ n) − 1, and B = O(log M + log³ n), so poly(B) and poly(log M + log³ n) are one class
--   - encoding: B = O(log M + log³ n), n sufficiently large → B ≤ C·(⌊log₂ M⌋ + (⌊log₂ n⌋+1)³ + 1), n ≥ n₀; reason: the meaning of O and of "sufficiently large"; constants depend on q
--   - encoding: machine unnamed → M one bit per cell, W ≥ b(⌊log₂ n⌋ + ⌊log₂(⌊log₂ M⌋+1)⌋ + 1); reason: M may exceed the word, and a word must address the bits of p
-- source:
--   Henzinger, Ragavan, Doubly-Efficient Private Information Retrieval from Modular Forms, STOC 2027 submission (manuscript sha256 2442f3db…), Lemma 9.5, p.35 (PDF pp.39–40)

import Mathlib
import Definitions.Def_ModFormPIR_Layouts

open MeasureTheory
open scoped ENNReal

set_option autoImplicit false

namespace ModFormPIR

/-- **Lemma 9.5** (Primes just above a power of two), p.35. Henzinger, Ragavan, *Doubly-Efficient Private Information Retrieval from Modular Forms*, STOC 2027 submission (manuscript sha256 2442f3db…).
For a fixed prime `q`, a randomized algorithm takes a positive `M` and a sufficiently large `n`, and constructs `B` and a prime `p ≡ 1 (mod q)` with
`p > M`, `p ≥ n⁴`, `2^B < p ≤ 2^B(1 + 1/(4n))`, `B = O(log M + log³ n)`, in expected time `poly(B)`.

**Formalization Note.** Las Vegas: every accepting run outputs valid `(B, p)`, and the accept time is measurable with finite expectation. The bound
`poly(log M + log³ n)` is `poly(B)`: the constraints force `B` above `log₂ M - 1` and `4 log₂ n - 1`, and below a constant times `log M + log³ n`, so the two
classes coincide. `M` may exceed the word, so it is input bit by bit. Output: `B` in cell `-1`, the `B + 1` bits of `p` from cell `-2` down. -/
theorem lemma_9_5 (q : ℕ) (hq : q.Prime) :
    ∃ (P : Program) (b C e n₀ : ℕ), NoProbe P ∧
      ∀ M n : ℕ, 0 < M → n₀ ≤ n →
      ∀ W ≥ b * (Nat.log2 n + Nat.log2 (Nat.log2 M + 1) + 1),
        Measurable (acceptCost P W (primeInput n M)) ∧
        ∫⁻ τ, acceptCost P W (primeInput n M) τ ∂coinMeasure ≤
          ((C * (Nat.log2 M + (Nat.log2 n + 1) ^ 3 + 1) ^ e : ℕ) : ℝ≥0∞) ∧
        ∀ (τ : ℕ → Bool) (t : ℕ) (st : State W), Accepts P [] τ (primeInput n M) t st →
          ∃ B p : ℕ, (st.mem (-1)).toNat = B ∧ BitCellsOK st (-2) (B + 1) ∧
            readNat st (-2) (B + 1) = p ∧
            p.Prime ∧ p ≡ 1 [MOD q] ∧ M < p ∧ n ^ 4 ≤ p ∧ 2 ^ B < p ∧
            (p : ℝ) ≤ 2 ^ B * (1 + 1 / (4 * (n : ℝ))) ∧
            B ≤ C * (Nat.log2 M + (Nat.log2 n + 1) ^ 3 + 1) := by sorry

end ModFormPIR
