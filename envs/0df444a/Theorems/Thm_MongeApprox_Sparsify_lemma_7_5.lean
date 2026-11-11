-- Prove2me | Theorems.Thm_MongeApprox_Sparsify_lemma_7_5
-- name    : MongeApprox.Sparsify.lemma_7_5
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T15:03:14.149568+00:00
-- url     : https://prove2.me/theorems/0f6f3800-c01b-4954-85b3-fe7dfe4ce10f
-- title:
--   Lemma 7.5 — rectangle replacement by a staircase with at most r + c − 1 nonzeros, computed in O(r + c) time
-- statement:
--   There are $C>0$ and an admissible program $P$ such that the following holds. Let $\mu$ be a nonnegative matrix supported on a rectangle $R$, with $r\ge1$ nonzero rows and $c\ge1$ nonzero columns. There is a nonnegative matrix $\widehat\mu$ supported on $R$ with the same row and column sums as $\mu$ and at most $r+c-1$ nonzero entries such that, for all integers $i$ and $j$, $\mu(Q_{ij})\le\widehat\mu(Q_{ij})\le\mu(R)$, and the first inequality is an equality unless $(i,j)$ lies strictly inside $R$. Given $r$, $c$ and the nonzero row sums and the nonzero column sums of $\mu$ in order, $P$ computes the nonzero entries of this $\widehat\mu$ within $C(r+c)$ steps.
--
--   Differences from the source:
--   - encoding: a nonnegative matrix µ supported on R (positions outside the matrix have mass zero) → µ : ℤ × ℤ → ℝ, nonnegative, zero outside R; reason: a matrix is its extension by zero to ℤ²; the same instances
--   - encoding: at most r + c − 1 nonzero entries → nonzeroCount µ̂ R + 1 ≤ r + c; reason: natural-number arithmetic without truncated subtraction; equivalent
--   - encoding: given the nonzero row and column sums of µ in order → input: integer cells r, c; real cells: the nonzero row sums in increasing row order, then the nonzero column sums in increasing column order; reason: a declared input layout; 'in order' read as increasing index
--   - generalization: the nonzero values of µ̂ can be computed → the output lists every nonzero entry of the same µ̂ exactly once with its position (rank of its row and of its column) and its value; reason: positions are output in addition to the values, which is more than the source asks and contains it
--   - encoding: O(r + c) time → halts within C·(r + c) steps, C fixed before µ and R; reason: explicit constant for O(·)
--   - generalization: word RAM with Ω(log N)-bit words extended with real registers (§3 Model of Computation, p. 18 / PDF 20) → the mission's `Program` on `SmaleNinth` core + integer ±, integer memory, int→real cast, `entry`, `halt`; rational literals only; no integer ×/÷/bit operations; reason: fewer operations and literals than the paper's machine, so an existence claim over these programs is stronger and implies the source's
--   - reading: word RAM with machine words of Ω(log N) bits, a lower bound on the word length only (§3 Model of Computation, p. 18 / PDF 20) → integer registers and integer memory cells hold unbounded integers (ℤ); every register and every memory cell not holding input is initially 0; reason: the paper bounds the word length only from below and leaves the initial memory content unspecified; zero-initialized memory is the usual RAM convention
-- source:
--   Gorbachev 2026, Edit Distance Approximation: Subquadratic Factor Three and Monge Approximation Schemes (PDF sha256 b7eeb435…), Lemma 7.5, printed p. 36 (PDF 38)

import Mathlib
import Definitions.Def_SmaleNinth_RealRAM
import Definitions.Def_MongeApprox_Sparsify_Quadrant
import Definitions.Def_MongeApprox_Sparsify_Machine

namespace MongeApprox.Sparsify

/-- Lemma 7.5 (rectangle replacement). There are `C > 0` and an admissible program `P` such that
for every nonnegative `µ` supported on a rectangle `R` with `r ≥ 1` nonzero rows and `c ≥ 1`
nonzero columns there is a nonnegative `µ̂` supported on `R` with the same row and column sums, at
most `r + c − 1` nonzero entries, and `µ(Q_ij) ≤ µ̂(Q_ij) ≤ µ(R)` for all integers `i, j`, with
equality in the first inequality unless `(i, j)` lies strictly inside `R`; and `P`, given `r`, `c`
and the nonzero row sums and nonzero column sums of `µ` in increasing order of index, halts within
`C · (r + c)` steps and outputs the nonzero entries of this `µ̂` (as row rank, column rank, value). -/
theorem lemma_7_5 :
    ∃ C : ℝ, 0 < C ∧ ∃ P : Program, Admissible P ∧
      ∀ (μ : ℤ × ℤ → ℝ) (R : Rect),
        (∀ z, 0 ≤ μ z) → (∀ z, z ∉ R.toSet → μ z = 0) →
        1 ≤ (nonzeroRows μ R).card → 1 ≤ (nonzeroCols μ R).card →
        ∃ μhat : ℤ × ℤ → ℝ, IsRectReplacement μ R μhat ∧
          HaltsWithin P (0 : Matrix (Fin 0) (Fin 0) ℝ)
            (init [((nonzeroRows μ R).card : ℤ), ((nonzeroCols μ R).card : ℤ)]
              (((nonzeroRows μ R).sort (· ≤ ·)).map (rowSum μ) ++
                ((nonzeroCols μ R).sort (· ≤ ·)).map (colSum μ)))
            (C * ((nonzeroRows μ R).card + (nonzeroCols μ R).card))
            (OutputsReplacement ((nonzeroRows μ R).sort (· ≤ ·))
              ((nonzeroCols μ R).sort (· ≤ ·)) μhat) := by sorry

end MongeApprox.Sparsify
