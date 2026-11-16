-- Prove2me | Theorems.Thm_LinSysAmp_Supplement_theorem_5_1
-- name    : LinSysAmp.Supplement.theorem_5_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T02:50:17.520026+00:00
-- url     : https://prove2.me/theorems/fa12247a-292f-48b0-9e81-1fd1d83f00ff
-- title:
--   Theorem 5.1 — worst-case matrix multiplication from an average-case algorithm
-- statement:
--   Let $\mathbb F_q$ be a finite field and $n\ge1$. Let $O$ be an algorithm, taking time $T$ per call, that solves $\mathrm{MM}_{n,q}$ with probability at least $\alpha>0$:
--   $$\Pr_{A,B\leftarrow\mathbb F_q^{n\times n},\,O}[O(A,B)=AB]\ge\alpha,$$
--   with $A,B$ independent and uniform. For every $0<\delta<1/2$ there is an algorithm which makes $O(\alpha^{-1}\log(1/\delta))$ calls to $O$, all on pairs of $n\times n$ matrices over $\mathbb F_q$, runs in time
--   $$O\Big(\frac{T+n^2}{\alpha}\log\frac1\delta\Big),$$
--   and solves the worst-case problem $\mathrm{MM}^{\mathrm{wc}}_{n,q}$ with probability at least $1-\delta$: for every pair $(A,B)$ it outputs $AB$ with probability at least $1-\delta$.
--
--   This is a worst-case to average-case reduction for matrix multiplication with only $O(1/\alpha)$ overhead, so average-case hardness of matrix multiplication at any constant success rate is as strong as worst-case hardness.
--
--   **Formalization Note** The algorithm is a program of the supplement's oracle machine with the MM interface; the input is $A$ then $B$ row-major and the output is the list of entries of the product. The program and its parameters are chosen for the field before $n$, $\alpha$, $\delta$ and the oracle.
--
--   Differences from the source:
--   - encoding: running time O((T + n²)/α · log(1/δ)) for a time-T oracle → on every run: calls ≤ C·α⁻¹·log(1/δ), field operations ≤ C·n²·α⁻¹·log(1/δ); reason: the oracle's cost T is charged per call, so the two bounds give the printed time bound; the machine counts calls and field operations separately
--   - reading: an O(·) bound with an unnamed constant and "there is an algorithm" → one absolute constant C, chosen before the field, and one program per field chosen before n, the parameters and the oracle; reason: the proof's constants are absolute and the reduction is black-box and uniform; this is the standard reading of O(·)
--   - generalization: the cost (and correctness) guarantees are stated for an oracle with the assumed success probability α → they hold for every oracle; only the success guarantee assumes the success probability α; reason: the reduction's cost never depends on the oracle's quality; the source's instance is the special case
--   - encoding: α unconstrained above → α ≤ 1 added; reason: the hypothesis α ≤ Pr[O(A,B) = AB] already forces it; without it the unconditional cost bounds could not be met for large α
--   - encoding: "All calls are made on pairs of n × n matrices over F_q" → the MM interface reads exactly two n × n matrices per call; reason: the oracle has type n × n matrices → n × n matrices, so no other call is possible
--   - encoding: n is an integer dimension → 1 ≤ n; reason: §3.1 fixes n ≥ 1 ("For an integer n ≥ 1")
-- source:
--   Couteau, Melissaris, Radhika Sajith, Hardness Self-Amplification in Linear Algebra and Fine-Grained Cryptography, arXiv:2611.04680 (version held, sha256 af7a90ac…), Theorem 5.1, p.23 (PDF p.25)

import Mathlib
import Definitions.Def_LinSysAmp_Supplement_OracleMachine
import Definitions.Def_LinSysAmp_Supplement_Problems

set_option autoImplicit false

open Matrix

namespace LinSysAmp.Supplement

universe u

/-- Theorem 5.1 (Worst-case to average-case reduction for matrix multiplication), p.23 (PDF p.25).
Couteau, Melissaris, Radhika Sajith, *Hardness Self-Amplification in Linear Algebra and Fine-Grained
Cryptography*, arXiv:2611.04680 (version held, sha256 af7a90ac…).

"Let O be a time-T algorithm that solves MM_{n,q} with probability at least α > 0. For every
0 < δ < 1/2, there is an algorithm which makes O(α⁻¹ log(1/δ)) calls to O, runs in time
O((T + n²)/α · log(1/δ)), and solves MM^wc_{n,q} with probability at least 1 − δ. All calls are made
on pairs of n × n matrices over F_q."

**Formalization Note.**
* *Algorithm.* A program `P` of the machine `LinSysAmp.Supplement.OracleMachine` with the MM
  interface `mmIface O` (every call reads two `n × n` matrices and returns an `n × n` matrix, so
  every call is made on pairs of `n × n` matrices). The input is `A` then `B`, row-major, from
  address `0`; the index registers hold `par n α δ`. The program and `par` are chosen for the
  field `F` only, before `n`, `α`, `δ` and the oracle ("we assume […] that the success probability α
  is known", p.23). The output is the list of the entries of the product, row-major.
* *Constants.* One absolute constant `C`, chosen before the field, bounds both `O(·)`.
* *Time.* On every run, for every oracle and every input, the program halts within the step budget
  with at most `C α⁻¹ log(1/δ)` calls and `C n² α⁻¹ log(1/δ)` field operations; with a time-`T`
  oracle the total time is at most `C α⁻¹ log(1/δ)·(T + n²)`.
* *Worst case.* `MM^wc_{n,q}` with probability `1 − δ`: for every pair `(A, B)` (not only on average)
  the run outputs `AB` with probability at least `1 − δ`.
* "Solves `MM_{n,q}` with probability `α`" is `α ≤ mmSuccess O` (Definition 3.2: `A, B` uniform in
  `F^{n×n}`). `n ≥ 1` (§3.1).
* `α ≤ 1` is added: the hypothesis `α ≤ mmSuccess O` already forces it; the cost clause holds
  for every oracle, and without it the bound `C α⁻¹ log(1/δ)` could fall below one step. -/
theorem theorem_5_1 :
    ∃ C : ℝ, 0 < C ∧ ∀ (F : Type u) [Field F] [Fintype F] [DecidableEq F],
      ∃ P : OProgram F, ∃ par : ℕ → ℝ → ℝ → List ℤ,
        ∀ n : ℕ, 1 ≤ n → ∀ α δ : ℝ, 0 < α → α ≤ 1 → 0 < δ → δ < 1 / 2 → ∀ O : MMOracle n F,
          let Bc : ℝ := C / α * Real.log (1 / δ)
          let Bo : ℝ := C * (n : ℝ) ^ 2 / α * Real.log (1 / δ)
          let N : ℕ := stepBudget Bc Bo
          (∀ A B : Matrix (Fin n) (Fin n) F,
            OHaltsWithin (mmIface O) P (oinit (par n α δ) (flatMat A ++ flatMat B)) N Bc Bo) ∧
          (α ≤ mmSuccess O → ∀ A B : Matrix (Fin n) (Fin n) F,
            1 - δ ≤ oOutputProb (mmIface O) P (oinit (par n α δ) (flatMat A ++ flatMat B)) N
              (.vec (flatMat (A * B)))) := by sorry

end LinSysAmp.Supplement
