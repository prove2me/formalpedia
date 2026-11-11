-- Prove2me | Theorems.Thm_LowRankShifts_MatPoly_corollary_2_12
-- name    : LowRankShifts.MatPoly.corollary_2_12
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T18:58:15.914637+00:00
-- url     : https://prove2.me/theorems/f78b89cc-021d-4cce-a6ac-a7dbe1d3f036
-- title:
--   Corollary 2.12 — worst-case to (1 − 2^{−d}/10)-average-case reduction for a matrix polynomial with 2^{d+1} − 1 queries
-- statement:
--   Let $F$ be a finite field and $P\in F\langle X_1,\dots,X_\ell,\cdot^T\rangle$ a matrix polynomial of degree $d$. There is a universal constant $C$ and, for each $F$ and $P$, one program $B$ of the machine `LowRankShifts_MatPoly_Machine` taking as input $M=(M_1,\dots,M_\ell)\in(F^{n\times n})^\ell$ (for every $n$) such that, for every (possibly randomized, memoryless) oracle $D:(F^{n\times n})^\ell\to F^{n\times n}$: every run halts after at most $C\,2^d\ell n^2+C$ operations and exactly $2^{d+1}-1$ queries, and
--
--   $$\Pr_{A\sim(F^{n\times n})^\ell}[D(A)=P(A)]\ \ge\ 1-\frac{2^{-d}}{10}\quad\Longrightarrow\quad\Pr[B(M)=P(M)]\ \ge\ \frac45 .$$
--
--   It applies Lemma 2.11 to the map $M\mapsto P(M)$, whose entries are polynomials of degree at most $d$ in the entries of $M$. Theorem 3.4 runs it with Theorem 3.5's amplifier as its oracle.
--
--   **Formalization Note.** `tupleInput M` stores $M_1,\dots,M_\ell$ row-major in consecutive blocks with $n$ in index register $0$; the oracle is `matOracle D`; $s$ and $d$ are `size P` and `degree P`.
--
--   Differences from the source:
--   - encoding: a randomized (oracle) algorithm whose time is its number of field operations (p. 8) → a `Program` of the machine `LowRankShifts_MatPoly_Machine` (field operations, index operations without multiplication or field↔index conversion, a vector oracle); time = the `ops` counter, queries = the `queries` counter; `sample` draws from the uniform law on the field; reason: the paper names no machine; this one charges every field and index operation one unit and cannot pack a matrix into one integer
--   - encoding: input matrices M = (M_1, …, M_ℓ) → the matrices row-major in consecutive field blocks from address 0, their start addresses in the index memory, and n in index register 0 (`tupleInput M`); the output n × n matrix is read row-major from the address designated by `haltOut`; reason: a fixed input/output convention of the machine; it carries no information beyond the input
--   - encoding: a (possibly randomized) oracle C : (F^{n×n})^ℓ → F^{n×n} → a memoryless PMF-valued oracle, every query an independent draw from the law of its answer (`matOracle D`: the vector oracle reading the ℓ matrices row-major, block after block, and writing the answer row-major); reason: the paper's oracles answer each query with fresh randomness (proof of Theorem 3.5, p. 21); a deterministic oracle is the case of point masses
--   - generalization: a polynomial P with degree d and s monomials → `P : MatPolynomial F ℓ`, any list of (coefficient, word) pairs; s = `size P` (list length), d = `degree P` (maximal word length); reason: the paper represents polynomials as lists of monomials (p. 8); Lean admits every list, including repeated words and zero coefficients, whose s and d may exceed those of the polynomial it represents; a list in which each word occurs once with a nonzero coefficient has the polynomial's own s and d, so the statement specializes to the paper's
--   - reading: runs in time O(2^dℓn^2) → every run halts with ops ≤ C·2^d·ℓ·n² + C, the constant fixed before every other quantity (field, polynomial, dimensions, inputs, oracle); reason: worst-case reading of O(·) as C·f + C on every run; time counts field operations at unit cost (p. 8), so the constant does not depend on the field
--   - reading: makes 2^{d+1} − 1 oracle queries → every run makes at most and exactly 2^{d+1} − 1 queries; reason: the count is stated as an exact number
--   - encoding: Pr[B(·) = ·] over the algorithm's coins and the oracle's answers → `probOut` of the run law after the step budget (`finalLaw`): the probability that the run halts with `haltOut` and the designated output equals the target; ⊥ (`halt`) counts as failure; reason: all runs halt within the budget (first conjunct), so this is the probability over complete runs
-- source:
--   Golovnev, Nagargoje, Shinkar, Singh, Stephens-Davidowitz, Worst-Case to Average-Case Reductions for Linear Algebra: Optimal, Simple, and General, STOC 2027 submission (manuscript sha256 ebcf9677…), p. 14 (PDF 17), Corollary 2.12

import Mathlib
import Definitions.Def_LowRankShifts_MatPoly_MatPoly
import Definitions.Def_LowRankShifts_MatPoly_Machine
import Definitions.Def_LowRankShifts_MatPoly_Inputs

set_option autoImplicit false

universe u

namespace LowRankShifts.MatPoly

/-- Corollary 2.12 (p. 14): for a finite field `F` and a matrix polynomial `P` of degree `d`, one
program `B` that, on input `M ∈ (F^{n×n})^ℓ`, for every (possibly randomized, memoryless) oracle
`D`, halts on every run within `C·2^d·ℓ·n² + C` operations after exactly `2^{d+1} − 1` queries,
and outputs `P(M)` with probability at least `4/5` whenever
`Pr_{A ∼ (F^{n×n})^ℓ}[D(A) = P(A)] ≥ 1 − 2^{−d}/10`. -/
theorem corollary_2_12 :
    ∃ C : ℝ, ∀ (F : Type u) [Field F] [Fintype F] [DecidableEq F] (ℓ : ℕ)
      (P : MatPolynomial F ℓ),
      ∃ B : Program F, ∀ (n : ℕ) (M : Fin ℓ → Matrix (Fin n) (Fin n) F)
        (D : (Fin ℓ → Matrix (Fin n) (Fin n) F) → PMF (Matrix (Fin n) (Fin n) F)),
        let T : ℝ := C * 2 ^ degree P * (ℓ : ℝ) * (n : ℝ) ^ 2 + C
        let Q : ℝ := 2 ^ (degree P + 1) - 1
        RunsWithin (PMF.uniformOfFintype F) (matOracle D) B (tupleInput M) T Q ∧
        (∀ σ ∈ (finalLaw (PMF.uniformOfFintype F) (matOracle D) B (tupleInput M) T Q).support,
          σ.queries = 2 ^ (degree P + 1) - 1) ∧
        (1 - (2 : ℝ) ^ (-(degree P : ℤ)) / 10 ≤ succProb P D →
          4 / 5 ≤ probOut (finalLaw (PMF.uniformOfFintype F) (matOracle D) B (tupleInput M) T Q)
            (outMat n n) (some (eval P M))) := by sorry

end LowRankShifts.MatPoly
