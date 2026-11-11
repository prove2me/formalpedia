-- Prove2me | Theorems.Thm_LowRankShifts_MatPoly_theorem_3_4
-- name    : LowRankShifts.MatPoly.theorem_3_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T18:58:09.793292+00:00
-- url     : https://prove2.me/theorems/6b70c449-9bc9-4412-9f2b-f022e5deb819
-- title:
--   Theorem 3.4 — any degree-d ≥ 2 matrix polynomial in the worst case from an α-average-case oracle with O(d2^d/α) queries
-- statement:
--   There are universal constants $C$ and $k$ such that for every prime $p$ and every matrix polynomial $P\in\mathbb F_p\langle X_1,\dots,X_\ell,\cdot^T\rangle$ with degree $d\ge 2$ and $s$ monomials there is one program $B$ of the machine `LowRankShifts_MatPoly_Machine` taking as input matrices $M=(M_1,\dots,M_\ell)\in(\mathbb F_p^{n\times n})^\ell$ (for every $n$) and a success-probability lower bound $\alpha\in(0,1/2)$, such that for every (possibly randomized, memoryless) oracle $D:(\mathbb F_p^{n\times n})^\ell\to\mathbb F_p^{n\times n}$: every run of $B$ halts after at most
--
--   $$C\,(\ell+s+d)^k\,2^{2d}\,n^2\,\frac{\log(1/\alpha)}{\alpha}+C\ \text{ operations and }\ C\,\frac{d\,2^d}{\alpha}+C\ \text{ oracle queries},$$
--
--   and
--
--   $$\Pr_{A\sim(\mathbb F_p^{n\times n})^\ell}[D(A)=P(A)]\ \ge\ \alpha\quad\Longrightarrow\quad\Pr[B(M,\alpha)=P(M)]\ \ge\ \frac45 ,$$
--
--   the left probability over a uniform $A$ and $D$'s randomness, the right one over $B$'s samples and $D$'s answers, for every fixed $M$.
--
--   This is the paper's first main result (Theorem 1.2 in the introduction): computing any matrix polynomial of degree at least two correctly on a small fraction $\alpha$ of inputs is as hard, up to $O_d(1/\alpha)$ calls and $O_{\ell,d}(n^2\log(1/\alpha)/\alpha)$ extra field operations, as computing it on every input. Matrix multiplication $X_1X_2$, squaring, Gram matrices and commutators are special cases.
--
--   **Formalization Note.** The program sees $n$ and $K=\lceil1/\alpha\rceil$ in index registers $0$, $1$ and $M$ row-major from address $0$ (`thresholdInput`); the output is the $n\times n$ matrix at the address designated by `haltOut`, $\bot$ being failure; the oracle is `matOracle D`; the hypothesis is `succProb P D ≥ α`; log is natural. The machine has no index multiplication and no field-to-index conversion, so no matrix product is available as a single instruction.
--
--   Differences from the source:
--   - encoding: a randomized (oracle) algorithm whose time is its number of field operations (p. 8) → a `Program` of the machine `LowRankShifts_MatPoly_Machine` (field operations, index operations without multiplication or field↔index conversion, a vector oracle); time = the `ops` counter, queries = the `queries` counter; `sample` draws from the uniform law on the field; reason: the paper names no machine; this one charges every field and index operation one unit and cannot pack a matrix into one integer
--   - encoding: input matrices M = (M_1, …, M_ℓ) → the matrices row-major in consecutive field blocks from address 0, their start addresses in the index memory, and n, K in index registers 0, 1 (`thresholdInput α M`); the output n × n matrix is read row-major from the address designated by `haltOut`; reason: a fixed input/output convention of the machine; it carries no information beyond the input
--   - generalization: B receives the real α ∈ (0, 1/2) → the program receives only K = ⌈1/α⌉ in index register 1 (register 0 holds n); the bounds and the hypothesis use α itself; reason: the machine has no real registers; a program that sees only K is in particular a program that sees α, so this specializes to the paper's statement
--   - encoding: a (possibly randomized) oracle D : (F_p^{n×n})^ℓ → F_p^{n×n} → a memoryless PMF-valued oracle, every query an independent draw from the law of its answer (`matOracle D`: the vector oracle reading the ℓ matrices row-major, block after block, and writing the answer row-major); reason: the paper's oracles answer each query with fresh randomness (proof of Theorem 3.5, p. 21); a deterministic oracle is the case of point masses
--   - generalization: a polynomial P with degree d and s monomials → `P : MatPolynomial F ℓ`, any list of (coefficient, word) pairs; s = `size P` (list length), d = `degree P` (maximal word length); reason: the paper represents polynomials as lists of monomials (p. 8); Lean admits every list, including repeated words and zero coefficients, whose s and d may exceed those of the polynomial it represents; a list in which each word occurs once with a nonzero coefficient has the polynomial's own s and d, so the statement specializes to the paper's
--   - encoding: log(1/α) (no base given) → `Real.log (1 / α)`, the natural logarithm; reason: another base changes only the universal constant
--   - reading: runs in time poly(ℓ, s, d)2^{2d}n^2 log(1/α)/α and makes O(d2^d/α) queries → every run halts with ops ≤ C·(ℓ + s + d)^k·2^{2d}·n²·log(1/α)/α + C and queries ≤ C·d·2^d/α + C, with C and k universal (fixed before p, ℓ, P, n, α, M, D); reason: worst-case reading of poly(·) and O(·) as C·(ℓ + s + d)^k and C·f + C on every run; the time counts field operations (p. 8)
--   - encoding: Pr[B(·) = ·] over the algorithm's coins and the oracle's answers → `probOut` of the run law after the step budget (`finalLaw`): the probability that the run halts with `haltOut` and the designated output equals the target; ⊥ (`halt`) counts as failure; reason: all runs halt within the budget (first conjunct), so this is the probability over complete runs
-- source:
--   Golovnev, Nagargoje, Shinkar, Singh, Stephens-Davidowitz, Worst-Case to Average-Case Reductions for Linear Algebra: Optimal, Simple, and General, STOC 2027 submission (manuscript sha256 ebcf9677…), pp. 18–19 (PDF 21–22), Theorem 3.4

import Mathlib
import Definitions.Def_ZamirInversion581_Mult_Uniform
import Definitions.Def_LowRankShifts_MatPoly_MatPoly
import Definitions.Def_LowRankShifts_MatPoly_Machine
import Definitions.Def_LowRankShifts_MatPoly_Inputs

set_option autoImplicit false

namespace LowRankShifts.MatPoly

/-- Theorem 3.4 (pp. 18–19): universal constants `C, k`; for every prime `p` and every matrix
polynomial `P` with transposes, of degree `d ≥ 2` with `s` monomials in `ℓ` variables, one program
`B` that, on input `M ∈ (F_p^{n×n})^ℓ` and `α ∈ (0, 1/2)` (as `K = ⌈1/α⌉`), for every (possibly
randomized, memoryless) oracle `D`, halts on every run within
`C·(ℓ + s + d)^k·2^{2d}·n²·log(1/α)/α + C` operations and `C·d·2^d/α + C` queries, and outputs
`P(M)` with probability at least `4/5` whenever `Pr_{A ∼ (F_p^{n×n})^ℓ}[D(A) = P(A)] ≥ α`. -/
theorem theorem_3_4 :
    ∃ (C : ℝ) (k : ℕ), ∀ (p : ℕ) [Fact p.Prime] (ℓ : ℕ) (P : MatPolynomial (ZMod p) ℓ),
      2 ≤ degree P →
      ∃ B : Program (ZMod p), ∀ (n : ℕ) (α : ℝ), 0 < α → α < 1 / 2 →
        ∀ (M : Fin ℓ → Matrix (Fin n) (Fin n) (ZMod p))
          (D : (Fin ℓ → Matrix (Fin n) (Fin n) (ZMod p)) → PMF (Matrix (Fin n) (Fin n) (ZMod p))),
          let T : ℝ := C * ((ℓ : ℝ) + size P + degree P) ^ k * 2 ^ (2 * degree P) * (n : ℝ) ^ 2 *
            Real.log (1 / α) / α + C
          let Q : ℝ := C * (degree P : ℝ) * 2 ^ degree P / α + C
          RunsWithin (PMF.uniformOfFintype (ZMod p)) (matOracle D) B (thresholdInput α M) T Q ∧
          (α ≤ succProb P D →
            4 / 5 ≤ probOut (finalLaw (PMF.uniformOfFintype (ZMod p)) (matOracle D) B
              (thresholdInput α M) T Q) (outMat n n) (some (eval P M))) := by sorry

end LowRankShifts.MatPoly
