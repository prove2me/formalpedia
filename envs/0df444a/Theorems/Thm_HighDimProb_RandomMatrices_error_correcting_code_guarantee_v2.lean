-- Prove2me | Theorems.Thm_HighDimProb_RandomMatrices_error_correcting_code_guarantee_v2
-- name    : HighDimProb.RandomMatrices.error_correcting_code_guarantee_v2
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-10-06T06:19:44.204414+00:00
-- url     : https://prove2.me/theorems/29c6fce3-6975-4fe6-a7fb-316617d384e4
-- title:
--   Theorem 4.3.5 — Guarantees for an error correcting code (corrected: $2r \le n$)
-- statement:
--   This is **Theorem 4.3.5** of Vershynin's *High-Dimensional Probability*: the coding-theoretic application of the packing/covering machinery of §4.2, in which covering numbers of the Hamming cube $(\{0,1\}^n, d_H)$ control a concrete combinatorial guarantee.
--
--   Assume positive integers $k, n, r$ with $2r \le n$ satisfy
--   $$
--   n \;\ge\; k + 2r \log_2\!\left(\frac{en}{2r}\right).
--   $$
--   Then there exists an error correcting code that encodes $k$-bit strings into $n$-bit strings and can correct $r$ errors: maps $E:\{0,1\}^k\to\{0,1\}^n$ and $D:\{0,1\}^n\to\{0,1\}^k$ such that $D(y)=x$ for every word $x\in\{0,1\}^k$ and every string $y\in\{0,1\}^n$ that differs from $E(x)$ in at most $r$ bits (Definition 4.3.3, `IsErrorCorrectingCode`, with $d_H$ the Hamming distance `hammingDist`).
--
--   **Formalization Note.** The retired version transcribed the printed hypothesis verbatim, which admits $2r>n$ — e.g. $(k,n,r)=(1,1,2)$, where $\log_2(e/4)<0$ makes the inequality hold — although no code with two codewords can correct $r\ge n/2$ errors, so it was disproved. The new statement adds the hypothesis $2r\le n$ and is otherwise unchanged. This is a correction to the printed source: the book's proof applies Exercise 4.2.16 (covering numbers of the Hamming cube, stated only "for every integer $m\in[0,n]$") and the binomial-sum bound of Exercise 0.0.5 with $m=2r$, so $2r\le n$ is exactly the range in which the printed proof is valid, and with it the proof goes through verbatim: $P(\{0,1\}^n,d_H,2r)\ge N(\{0,1\}^n,d_H,2r)\ge 2^n\,(2r/en)^{2r}\ge 2^k$, then Lemma 4.3.4. (At $2r=n$ the hypothesis is unsatisfiable for $k\ge1$ since $\log_2 e>1$, so no degenerate instance remains.) $e$ is `Real.exp 1`, $\log_2$ is `Real.logb 2`, and $k,n,r>0$ as in the book's "positive integers".
-- source:
--   Vershynin, High-Dimensional Probability (CUP 2018), Theorem 4.3.5, p. 88 (PDF p. 96) — corrected transcription of the printed statement: the hypothesis 2r ≤ n (the range m = 2r ∈ [0, n] of Exercise 4.2.16 used in the proof) is added

import Mathlib
import Definitions.Def_HighDimProb_RandomMatrices_hammingDist
import Definitions.Def_HighDimProb_RandomMatrices_IsErrorCorrectingCode

namespace HighDimProb.RandomMatrices

/-- **Theorem 4.3.5** (Guarantees for an error correcting code), Vershynin, *High-Dimensional
Probability* (2018), p. 88 — **corrected statement**.

Assume that positive integers `k, n, r` with `2r ≤ n` are such that `n ≥ k + 2r log₂(en/(2r))`.
Then there exists an error correcting code that encodes `k`-bit strings into `n`-bit strings and
can correct `r` errors (Definition 4.3.3, `IsErrorCorrectingCode`).

Correction to the printed source: the book states the theorem without the restriction
`2r ≤ n`, but its proof applies Exercise 4.2.16 (and the binomial bound of Exercise 0.0.5)
with `m = 2r`, which are stated only "for every integer `m ∈ [0, n]`". Without `2r ≤ n` the
printed statement is false: for `(k, n, r) = (1, 1, 2)` the hypothesis holds (since
`log₂(e/4) < 0`) but no code with two codewords can correct `r ≥ n/2` errors (the accepted
disproof of the retired version). With `2r ≤ n` the printed proof goes through verbatim:
`P({0,1}ⁿ, d_H, 2r) ≥ N({0,1}ⁿ, d_H, 2r) ≥ 2ⁿ (2r/(en))^{2r} ≥ 2ᵏ`, then Lemma 4.3.4. -/
theorem error_correcting_code_guarantee_v2 (k n r : ℕ) (hk : 0 < k) (hn : 0 < n) (hr : 0 < r)
    (hrn : 2 * r ≤ n)
    (h : (n : ℝ) ≥ (k : ℝ) + 2 * (r : ℝ) * Real.logb 2 (Real.exp 1 * (n : ℝ) / (2 * (r : ℝ)))) :
    ∃ E : (Fin k → Bool) → (Fin n → Bool), ∃ D : (Fin n → Bool) → (Fin k → Bool),
      IsErrorCorrectingCode (r := r) E D := by sorry

end HighDimProb.RandomMatrices
