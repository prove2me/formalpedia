-- Prove2me | Theorems.Thm_LowRankShifts_MatPoly_theorem_2_5
-- name    : LowRankShifts.MatPoly.theorem_2_5
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T18:58:17.854869+00:00
-- url     : https://prove2.me/theorems/a0de7502-f0cb-458c-9de3-67b015e5a077
-- title:
--   Theorem 2.5 — generalized Freivalds verification of C = P(A) in O(ksdn²) time with one-sided error |F|^{−k}
-- statement:
--   Let $F$ be a finite field. There is a universal constant $C'$ and one program $R$ of the machine `LowRankShifts_MatPoly_Machine` taking as input a matrix polynomial $P\in F\langle X_1,\dots,X_\ell,\cdot^T\rangle$ with degree $d$ and $s$ monomials, a positive integer $k$, matrices $A=(A_1,\dots,A_\ell)\in(F^{n\times n})^\ell$ and $C\in F^{n\times n}$, such that every run halts after at most $C'ksdn^2+C'$ operations and no oracle query, and
--
--   $$P(A)=C\ \Longrightarrow\ \Pr[R(P,k,A,C)=\mathrm{YES}]=1,\qquad P(A)\ne C\ \Longrightarrow\ \Pr[R(P,k,A,C)=\mathrm{NO}]\ \ge\ 1-|F|^{-k}.$$
--
--   This is the verification step of the amplifier of Theorem 3.5: a candidate for $P(A)$ is accepted only if it passes $k$ random checks.
--
--   **Formalization Note.** `verifierInput P k A C` stores $A_1,\dots,A_\ell$, $C$ and the coefficients of $P$ as field blocks, the words of $P$ in the index memory, and $n,k,\ell,s$ in index registers $0$–$3$. YES is a halt by `haltOut`, NO a halt by `halt`. The statement is posed as printed; at $s=0$ or $d=0$ its time bound is $C'$, which no correct and sound verifier meets (see the mission's insights).
--
--   Differences from the source:
--   - encoding: a randomized algorithm whose time is its number of field operations (p. 8) → a `Program` of the machine `LowRankShifts_MatPoly_Machine` run with the uniform sampling law; time = the `ops` counter; it makes no oracle query (query bound 0, so the vector oracle `O : VecOracle F 0 0`, universally quantified, is never consulted); reason: the paper names no machine; R is not an oracle algorithm
--   - encoding: input P, k, A, C → `verifierInput P k A C`: A_1, …, A_ℓ, C row-major and the coefficients of P as field blocks, the words of P (length, then variable index and transpose flag of each letter) in the index memory after the block start addresses, n, k, ℓ, s in index registers 0–3; reason: a fixed input convention; P is an input, so one program serves every P
--   - generalization: a polynomial P with degree d and s monomials → `P : MatPolynomial F ℓ`, any list of (coefficient, word) pairs; s = `size P` (list length), d = `degree P` (maximal word length); reason: the paper represents polynomials as lists of monomials (p. 8); Lean admits every list, including repeated words and zero coefficients, whose s and d may exceed those of the polynomial it represents; a list in which each word occurs once with a nonzero coefficient has the polynomial's own s and d, so the statement specializes to the paper's
--   - reading: runs in time O(ksdn^2) → every run halts with ops ≤ C'·k·s·d·n² + C', the constant fixed before every other quantity (field, polynomial, dimensions, inputs, oracle); reason: worst-case reading of O(·) as C·f + C on every run; time counts field operations at unit cost (p. 8), so the constant does not depend on the field
--   - encoding: R(P, k, A, C) = YES / NO → the run halts by `haltOut` (verdict `some true`) / by `halt` (verdict `some false`), with probabilities read from the run law after the step budget; reason: all runs halt within the budget
-- source:
--   Golovnev, Nagargoje, Shinkar, Singh, Stephens-Davidowitz, Worst-Case to Average-Case Reductions for Linear Algebra: Optimal, Simple, and General, STOC 2027 submission (manuscript sha256 ebcf9677…), pp. 10–11 (PDF 13–14), Theorem 2.5

import Mathlib
import Definitions.Def_LowRankShifts_MatPoly_MatPoly
import Definitions.Def_LowRankShifts_MatPoly_Machine
import Definitions.Def_LowRankShifts_MatPoly_Inputs

set_option autoImplicit false

universe u

namespace LowRankShifts.MatPoly

/-- Theorem 2.5 (pp. 10–11, generalization of Freivalds' algorithm): for a finite field `F`, one
program `R` that takes as input a matrix polynomial `P` with degree `d` and `s` monomials, a
positive integer `k`, matrices `A ∈ (F^{n×n})^ℓ` and `C ∈ F^{n×n}`, halts on every run within
`C'·k·s·d·n² + C'` operations without oracle queries, says YES with probability `1` if
`P(A) = C`, and says NO with probability at least `1 − |F|^{−k}` if `P(A) ≠ C`. -/
theorem theorem_2_5 :
    ∃ C' : ℝ, ∀ (F : Type u) [Field F] [Fintype F] [DecidableEq F],
      ∃ R : Program F, ∀ (ℓ n : ℕ) (P : MatPolynomial F ℓ) (k : ℕ), 1 ≤ k →
        ∀ (A : Fin ℓ → Matrix (Fin n) (Fin n) F) (C : Matrix (Fin n) (Fin n) F)
          (O : VecOracle F 0 0),
          let T : ℝ := C' * (k : ℝ) * (size P : ℝ) * (degree P : ℝ) * (n : ℝ) ^ 2 + C'
          RunsWithin (PMF.uniformOfFintype F) O R (verifierInput P k A C) T 0 ∧
          (eval P A = C →
            probOut (finalLaw (PMF.uniformOfFintype F) O R (verifierInput P k A C) T 0)
              verdict (some true) = 1) ∧
          (eval P A ≠ C →
            1 - (Fintype.card F : ℝ) ^ (-(k : ℤ)) ≤
              probOut (finalLaw (PMF.uniformOfFintype F) O R (verifierInput P k A C) T 0)
                verdict (some false)) := by sorry

end LowRankShifts.MatPoly
