-- Prove2me | Theorems.Thm_LowRankShifts_MatPoly_theorem_3_5
-- name    : LowRankShifts.MatPoly.theorem_3_5
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T18:58:11.301417+00:00
-- url     : https://prove2.me/theorems/9f260146-766c-462b-8775-c284cb4ba0c8
-- title:
--   Theorem 3.5 — average-case amplification for a matrix polynomial from success α to 1 − 2^{−d}/10 with O(d/α) queries
-- statement:
--   There are universal constants $C$ and $k$ such that for every prime $p$ and every matrix polynomial $P\in\mathbb F_p\langle X_1,\dots,X_\ell,\cdot^T\rangle$ with degree $d\ge 2$ and $s$ monomials there is one program of the machine `LowRankShifts_MatPoly_Machine` — call it $\mathcal C$ — taking as input $A=(A_1,\dots,A_\ell)\in(\mathbb F_p^{n\times n})^\ell$ (for every $n$) and $\alpha\in(0,1/2)$, such that for every (possibly randomized, memoryless) oracle $D:(\mathbb F_p^{n\times n})^\ell\to\mathbb F_p^{n\times n}$: every run halts after at most $C(\ell+s+d)^k2^dn^2\log(1/\alpha)/\alpha+C$ operations and $C d/\alpha+C$ queries, and
--
--   $$\Pr_{A}[D(A)=P(A)]\ \ge\ \alpha\quad\Longrightarrow\quad\Pr_{A\sim(\mathbb F_p^{n\times n})^\ell}\big[\mathcal C(A,\alpha)=P(A)\big]\ \ge\ 1-\frac{2^{-d}}{10},$$
--
--   the right probability over a uniform $A$, $\mathcal C$'s samples and the oracle's answers.
--
--   This is the amplification half of the main theorem: an oracle that is right on an $\alpha$ fraction of inputs becomes one that is right on all but a $2^{-d}/10$ fraction, as Corollary 2.12 requires.
--
--   **Formalization Note.** The program sees $n$ and $K=\lceil1/\alpha\rceil$ in index registers $0$, $1$ and $A$ row-major from address $0$ (`thresholdInput`); the oracle is `matOracle D`; the hypothesis is `succProb P D ≥ α`; log is natural.
--
--   Differences from the source:
--   - encoding: a randomized (oracle) algorithm whose time is its number of field operations (p. 8) → a `Program` of the machine `LowRankShifts_MatPoly_Machine` (field operations, index operations without multiplication or field↔index conversion, a vector oracle); time = the `ops` counter, queries = the `queries` counter; `sample` draws from the uniform law on the field; reason: the paper names no machine; this one charges every field and index operation one unit and cannot pack a matrix into one integer
--   - encoding: input matrices M = (M_1, …, M_ℓ) → the matrices row-major in consecutive field blocks from address 0, their start addresses in the index memory, and n, K in index registers 0, 1 (`thresholdInput α M`); the output n × n matrix is read row-major from the address designated by `haltOut`; reason: a fixed input/output convention of the machine; it carries no information beyond the input
--   - generalization: B receives the real α ∈ (0, 1/2) → the program receives only K = ⌈1/α⌉ in index register 1 (register 0 holds n); the bounds and the hypothesis use α itself; reason: the machine has no real registers; a program that sees only K is in particular a program that sees α, so this specializes to the paper's statement
--   - encoding: a (possibly randomized) oracle D : (F_p^{n×n})^ℓ → F_p^{n×n} → a memoryless PMF-valued oracle, every query an independent draw from the law of its answer (`matOracle D`: the vector oracle reading the ℓ matrices row-major, block after block, and writing the answer row-major); reason: the paper's oracles answer each query with fresh randomness (proof of Theorem 3.5, p. 21); a deterministic oracle is the case of point masses
--   - generalization: a polynomial P with degree d and s monomials → `P : MatPolynomial F ℓ`, any list of (coefficient, word) pairs; s = `size P` (list length), d = `degree P` (maximal word length); reason: the paper represents polynomials as lists of monomials (p. 8); Lean admits every list, including repeated words and zero coefficients, whose s and d may exceed those of the polynomial it represents; a list in which each word occurs once with a nonzero coefficient has the polynomial's own s and d, so the statement specializes to the paper's
--   - encoding: log(1/α) (no base given) → `Real.log (1 / α)`, the natural logarithm; reason: another base changes only the universal constant
--   - reading: runs in time poly(ℓ, s, d)·2^dn^2 log(1/α)/α and makes O(d/α) queries → every run halts with ops ≤ C·(ℓ + s + d)^k·2^d·n²·log(1/α)/α + C and queries ≤ C·d/α + C, with C and k universal (fixed before p, ℓ, P, n, α, M, D); reason: worst-case reading of poly(·) and O(·) as C·(ℓ + s + d)^k and C·f + C on every run; the time counts field operations (p. 8)
--   - encoding: Pr_{A∼(F_p^{n×n})^ℓ}[C(A, α) = P(A)] → the uniform average over A of `probOut` of the run on `thresholdInput α A` (halt by `haltOut` with output P(A)); ⊥ counts as failure; reason: the probability over A, the program's samples and the oracle's answers
-- source:
--   Golovnev, Nagargoje, Shinkar, Singh, Stephens-Davidowitz, Worst-Case to Average-Case Reductions for Linear Algebra: Optimal, Simple, and General, STOC 2027 submission (manuscript sha256 ebcf9677…), p. 19 (PDF 22), Theorem 3.5

import Mathlib
import Definitions.Def_ZamirInversion581_Mult_Uniform
import Definitions.Def_LowRankShifts_MatPoly_MatPoly
import Definitions.Def_LowRankShifts_MatPoly_Machine
import Definitions.Def_LowRankShifts_MatPoly_Inputs

set_option autoImplicit false

namespace LowRankShifts.MatPoly

/-- Theorem 3.5 (p. 19): universal constants `C, k`; for every prime `p` and every matrix
polynomial `P` with transposes, of degree `d ≥ 2` with `s` monomials in `ℓ` variables, one program
that, on input `A ∈ (F_p^{n×n})^ℓ` and `α ∈ (0, 1/2)` (as `K = ⌈1/α⌉`), for every (possibly
randomized, memoryless) oracle `D`, halts on every run within
`C·(ℓ + s + d)^k·2^d·n²·log(1/α)/α + C` operations and `C·d/α + C` queries, and, whenever
`Pr_A[D(A) = P(A)] ≥ α`, satisfies `Pr_{A, coins}[output = P(A)] ≥ 1 − 2^{−d}/10`. -/
theorem theorem_3_5 :
    ∃ (C : ℝ) (k : ℕ), ∀ (p : ℕ) [Fact p.Prime] (ℓ : ℕ) (P : MatPolynomial (ZMod p) ℓ),
      2 ≤ degree P →
      ∃ B : Program (ZMod p), ∀ (n : ℕ) (α : ℝ), 0 < α → α < 1 / 2 →
        ∀ D : (Fin ℓ → Matrix (Fin n) (Fin n) (ZMod p)) → PMF (Matrix (Fin n) (Fin n) (ZMod p)),
          let T : ℝ := C * ((ℓ : ℝ) + size P + degree P) ^ k * 2 ^ degree P * (n : ℝ) ^ 2 *
            Real.log (1 / α) / α + C
          let Q : ℝ := C * (degree P : ℝ) / α + C
          (∀ A : Fin ℓ → Matrix (Fin n) (Fin n) (ZMod p),
            RunsWithin (PMF.uniformOfFintype (ZMod p)) (matOracle D) B (thresholdInput α A) T Q) ∧
          (α ≤ succProb P D →
            1 - (2 : ℝ) ^ (-(degree P : ℤ)) / 10 ≤
              ZamirInversion581.Mult.unifMean fun A : Fin ℓ → Matrix (Fin n) (Fin n) (ZMod p) =>
                probOut (finalLaw (PMF.uniformOfFintype (ZMod p)) (matOracle D) B
                  (thresholdInput α A) T Q) (outMat n n) (some (eval P A))) := by sorry

end LowRankShifts.MatPoly
