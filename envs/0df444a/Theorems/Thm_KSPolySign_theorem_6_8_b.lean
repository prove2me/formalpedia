-- Prove2me | Theorems.Thm_KSPolySign_theorem_6_8_b
-- name    : KSPolySign.theorem_6_8_b
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-24T14:19:46.901992+00:00
-- url     : https://prove2.me/theorems/79e08380-7bdd-4e64-83a7-8b53b86a2938
-- title:
--   Theorem 6.8(b): deterministic polynomial-time signing algorithm
-- statement:
--   This is part (b) of the main result (Theorem 6.8) of Song–Yue: a deterministic polynomial-time algorithm for rank-one matrix discrepancy.
--
--   There are one deterministic program $P$ on the unit-cost real RAM, using only rational literals and the operations $+,-,\times,\div$ and comparisons (no square roots, no random draws), and constants $C,k$, such that the following holds. For all $m$, all $n\ge1$ and all Hermitian $A_1,\dots,A_m\in\mathbb C^{n\times n}$ of rank at most one whose entries have rational real and imaginary parts, the run of $P$ on the input (the numbers $m,n$ followed by the real and imaginary parts of all entries)
--
--   1. halts after some number $t$ of steps with $t+1\le C(m+n+2)^k$;
--   2. performs at most $C\,(mn^2+n^{56})\,\log^k(m+n+2)$ real additions, subtractions, multiplications, divisions and comparisons;
--   3. outputs signs $\sigma_1,\dots,\sigma_m\in\{-1,1\}$ with
--   $$\Big\|\sum_{i=1}^m\sigma_iA_i\Big\|\le3.4814\,\Big\|\sum_{i=1}^mA_i^2\Big\|^{1/2}.$$
--
--   This is the algorithmic content of the paper (Algorithm 3): normalization and rounding (Lemmas 3.1, 4.3), grouped partial signing (Lemma 4.6) and a local search on the matrix potential driven by Lemma 6.3.
--
--   **Formalization Note** The statement is verbatim part (b) of `KSPolySign.theorem_6_8`: the machine is `MatMulTimeLP.RealRAM` restricted by `VecBalPoly.Admissible`, arithmetic operations are counted by `VecBalPoly.realOps`, the input is `layout m n A`, and the signs are the $m$ output cells. The bounds hold for every tape $\omega$ (the admissible program draws no randomness).
-- source:
--   Z. Song, S. Yue, Polynomial Time Algorithms for the Kadison-Singer Problem, arXiv:2609.19794 (held version, sha256 47d4aaa5…), Theorem 6.8(b), p.68 (PDF p.68); Theorem 1.1, p.3

import Mathlib
import Definitions.Def_AgnosticTNS_opNorm
import Definitions.Def_MatMulTimeLP_RealRAM
import Definitions.Def_VecBalPoly_Admissible
import Definitions.Def_VecBalPoly_realOps
import Definitions.Def_KSPolySign_IsRatC
import Definitions.Def_KSPolySign_layout
open Matrix
open scoped ComplexOrder

namespace KSPolySign

/-- **Theorem 6.8(b) (deterministic polynomial-time algorithm).** Song–Yue, *Polynomial Time Algorithms for the Kadison-Singer Problem*, arXiv:2609.19794 (held version, sha256 47d4aaa5…), Theorem 6.8(b), p.68 (PDF p.68); Theorem 1.1, p.3.
For rational Hermitian rank-at-most-one inputs, one deterministic admissible real-RAM program (Algorithm 3)
finds signs meeting the bound of (a) with `realOps ≤ C(mn² + n⁵⁶)(log(m + n + 2))^k` and total running
time at most `C(m + n + 2)^k`, `C, k` fixed before the input, `n ≥ 1`.
**Formalization Note** Verbatim part (b) of `KSPolySign.theorem_6_8`: `VecBalPoly.Admissible`
program on the published real RAM, input `layout m n A`, outputs the `m` cells after the input. -/
theorem theorem_6_8_b :
    (∃ P : MatMulTimeLP.Program, VecBalPoly.Admissible P ∧ ∃ C k : ℕ,
      ∀ (m n : ℕ), 1 ≤ n → ∀ A : Fin m → Matrix (Fin n) (Fin n) ℂ,
        (∀ i, (A i).IsHermitian ∧ (A i).rank ≤ 1 ∧ ∀ j l, IsRatC (A i j l)) →
        ∀ ω : MatMulTimeLP.Tape, ∃ t : ℕ, MatMulTimeLP.HaltsAt P (layout m n A) ω t ∧
          (VecBalPoly.realOps P (layout m n A) ω t : ℝ) ≤
            C * ((m : ℝ) * n ^ 2 + (n : ℝ) ^ 56) * Real.log (m + n + 2) ^ k ∧
          ((t + 1 : ℕ) : ℝ) ≤ C * ((m : ℝ) + n + 2) ^ k ∧
          (∀ i, MatMulTimeLP.outputAt P (layout m n A) ω t m i = 1 ∨ MatMulTimeLP.outputAt P (layout m n A) ω t m i = -1) ∧
          AgnosticTNS.opNorm (∑ i, ((MatMulTimeLP.outputAt P (layout m n A) ω t m i : ℝ) : ℂ) • A i) ≤
            3.4814 * Real.sqrt (AgnosticTNS.opNorm (∑ i, A i * A i))) := by sorry

end KSPolySign
