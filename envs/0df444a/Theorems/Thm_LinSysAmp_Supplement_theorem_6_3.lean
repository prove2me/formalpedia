-- Prove2me | Theorems.Thm_LinSysAmp_Supplement_theorem_6_3
-- name    : LinSysAmp.Supplement.theorem_6_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T02:52:42.566214+00:00
-- url     : https://prove2.me/theorems/8cf7c710-6e06-4cb7-975d-88789e498788
-- title:
--   Theorem 6.3 — worst-case matrix multiplication from an algorithm with expected agreement $1/q+\varepsilon$
-- statement:
--   Let $\mathbb F_q$ be a finite field and $n\ge1$. Let $O$ be an algorithm on pairs of $n\times n$ matrices, taking time $T$ per call, with expected agreement $1/q+\varepsilon$ for some $\varepsilon>0$:
--   $$\mathbb E_{A,B\leftarrow\mathbb F_q^{n\times n},\,O}[\mathrm{agr}(O(A,B),AB)]\ge\frac1q+\varepsilon,$$
--   where $\mathrm{agr}$ is the fraction of agreeing entries. For every $0<\delta<1/2$ there is an algorithm which makes $O(\varepsilon^{-2}\log(nq)\log(1/\delta))$ calls to $O$, all on pairs of $n\times n$ matrices over $\mathbb F_q$, runs in time
--   $$O\Big(\frac{T+n^2\log t}{\varepsilon^2}\log(nq)\log\frac1\delta\Big),\qquad t=\big\lceil6\varepsilon^{-2}\log(100n^2q)\big\rceil,$$
--   and outputs $AB$ with probability at least $1-\delta$, for every pair $(A,B)\in\mathbb F_q^{n\times n}\times\mathbb F_q^{n\times n}$.
--
--   Even an algorithm that gets only slightly more entries right than a random guess yields exact worst-case matrix multiplication.
--
--   **Formalization Note** As in Theorem 5.1, a program of the oracle machine with the MM interface, chosen for the field before $n$, $\varepsilon$, $\delta$ and the oracle ($\varepsilon$ is known, p.36).
--
--   Differences from the source:
--   - encoding: running time O((T + n² log t)/ε² · log(nq) log(1/δ)) for a time-T oracle → on every run: calls ≤ C·ε⁻²·log(nq)·log(1/δ), field operations ≤ C·n²·log t·ε⁻²·log(nq)·log(1/δ); reason: the oracle's cost T is charged per call, so the two bounds give the printed time bound; the machine counts calls and field operations separately
--   - reading: an O(·) bound with an unnamed constant and "there is an algorithm" → one absolute constant C, chosen before the field, and one program per field chosen before n, the parameters and the oracle; reason: the proof's constants are absolute and the reduction is black-box and uniform; this is the standard reading of O(·)
--   - generalization: the cost (and correctness) guarantees are stated for an oracle with the assumed expected agreement 1/q + ε → they hold for every oracle; only the success guarantee assumes the expected agreement 1/q + ε; reason: the reduction's cost never depends on the oracle's quality; the source's instance is the special case
--   - encoding: ε unconstrained above → ε ≤ 1 added; reason: the hypothesis 1/q + ε ≤ expected agreement ≤ 1 already forces it; without it the unconditional cost bounds could not be met for large ε
--   - encoding: "All calls are made on pairs of n × n matrices over F_q" → the MM interface reads exactly two n × n matrices per call; reason: the oracle has type n × n matrices → n × n matrices
--   - encoding: n is an integer dimension → 1 ≤ n; reason: §3.1 fixes n ≥ 1 ("For an integer n ≥ 1")
-- source:
--   Couteau, Melissaris, Radhika Sajith, Hardness Self-Amplification in Linear Algebra and Fine-Grained Cryptography, arXiv:2611.04680 (version held, sha256 af7a90ac…), Theorem 6.3, p.38 (PDF p.40)

import Mathlib
import Definitions.Def_LinSysAmp_Supplement_OracleMachine
import Definitions.Def_LinSysAmp_Supplement_Problems

set_option autoImplicit false

open Matrix

namespace LinSysAmp.Supplement

universe u

/-- Theorem 6.3 (Worst-case to average-case reduction from approximate algorithms), p.38
(PDF p.40). Couteau, Melissaris, Radhika Sajith, *Hardness Self-Amplification in Linear Algebra and
Fine-Grained Cryptography*, arXiv:2611.04680 (version held, sha256 af7a90ac…).

"Let O be a time-T algorithm with expected agreement 1/q + ε, for some ε > 0. For every
0 < δ < 1/2, there is an algorithm which makes O(ε⁻² log(nq) log(1/δ)) calls to O, runs in time
O((T + n² log t)/ε² · log(nq) log(1/δ)), where t = ⌈6ε⁻² log(100n²q)⌉, and outputs AB with
probability at least 1 − δ, for every pair (A, B) ∈ F_q^{n×n} × F_q^{n×n}. All calls are made on
pairs of n × n matrices over F_q."

**Formalization Note.**
* *Algorithm.* A program of the machine `LinSysAmp.Supplement.OracleMachine` with the MM interface
  `mmIface O` (every call is on a pair of `n × n` matrices). Input `A` then `B` row-major, index
  registers `par n ε δ`; program and `par` are chosen for the field only, before `n`, `ε`, `δ` and
  the oracle ("we assume that ε is known", p.36).
* *Constants.* One absolute constant `C`, chosen before the field, bounds both `O(·)`.
* *Time.* On every run, for every oracle and input: at most `C ε⁻² log(nq) log(1/δ)` calls and
  `C n² log t · ε⁻² log(nq) log(1/δ)` field operations, `t = ⌈6ε⁻² log(100n²q)⌉`. With a time-`T`
  oracle the total is within the printed bound.
* *Expected agreement* `1/q + ε` is `1/q + ε ≤ mmAgreement O` (§6.3, `A, B ← F^{n×n}`).
* *Worst case.* For every pair `(A, B)` the run outputs `AB` with probability at least `1 − δ`.
* `q = Fintype.card F`, `n ≥ 1` (§3.1), `log` natural.
* `ε ≤ 1` is added: the hypothesis `1/q + ε ≤ mmAgreement O ≤ 1` already forces it; the cost
  clause holds for every oracle, and without it `ε⁻²` could be made arbitrarily small. -/
theorem theorem_6_3 :
    ∃ C : ℝ, 0 < C ∧ ∀ (F : Type u) [Field F] [Fintype F] [DecidableEq F],
      ∃ P : OProgram F, ∃ par : ℕ → ℝ → ℝ → List ℤ,
        ∀ n : ℕ, 1 ≤ n → ∀ ε δ : ℝ, 0 < ε → ε ≤ 1 → 0 < δ → δ < 1 / 2 → ∀ O : MMOracle n F,
          let q : ℝ := Fintype.card F
          let t : ℕ := ⌈6 / ε ^ 2 * Real.log (100 * (n : ℝ) ^ 2 * q)⌉₊
          let Bc : ℝ := C / ε ^ 2 * Real.log (n * q) * Real.log (1 / δ)
          let Bo : ℝ := C * (n : ℝ) ^ 2 * Real.log t / ε ^ 2 * Real.log (n * q) * Real.log (1 / δ)
          let N : ℕ := stepBudget Bc Bo
          (∀ A B : Matrix (Fin n) (Fin n) F,
            OHaltsWithin (mmIface O) P (oinit (par n ε δ) (flatMat A ++ flatMat B)) N Bc Bo) ∧
          (1 / q + ε ≤ mmAgreement O → ∀ A B : Matrix (Fin n) (Fin n) F,
            1 - δ ≤ oOutputProb (mmIface O) P (oinit (par n ε δ) (flatMat A ++ flatMat B)) N
              (.vec (flatMat (A * B)))) := by sorry

end LinSysAmp.Supplement
