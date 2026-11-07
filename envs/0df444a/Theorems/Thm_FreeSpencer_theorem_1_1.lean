-- Prove2me | Theorems.Thm_FreeSpencer_theorem_1_1
-- name    : FreeSpencer.theorem_1_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:04:21.025208+00:00
-- url     : https://prove2.me/theorems/1395a699-e765-428b-bd9d-28e2ef2ed8df
-- title:
--   Theorem 1.1, p.2 — Matrix Spencer with the constant 4000 and a real-arithmetic algorithm
-- statement:
--   Let $A_1,\dots,A_n$ be real symmetric $m\times m$ matrices with operator norm $\|A_i\|\le1$. Then there are signs $\sigma\in\{-1,1\}^n$ with
--   $$\Bigl\|\sum_{i=1}^n\sigma_iA_i\Bigr\|\le4000\sqrt{n\max\{1,\,1+\log(2m/n)\}}.$$
--   Moreover there is one randomized real-arithmetic program such that, for all $n,m$, all such matrices and every integer $b\ge1$, it returns such a signing or reports failure, with failure probability at most $2^{-b}$, and every execution runs in time polynomial in $n,m,b$, with constants independent of the entries of the matrices.
--
--   This proves the Matrix Spencer conjecture, in its general form, with the optimal dependence on $m/n$.
--
--   **Formalization Note** The model is Definition B.1 without its eigendecomposition primitive, as Appendix F establishes: the published real RAM with rational literals and no Gaussian draw. The program and the constants $C,K$ come before $n,m,b$ and the matrices. Time is at most $C(n+m+b+2)^K$.
--
--   Differences from the source:
--   - reading: "the real-arithmetic model" (Definition B.1 without the eigendecomposition primitive, App. F) → MatMulTimeLP.RealRAM with Admissible programs: rational literals, no gauss; unit cost; input n, m, b as reals then the entries; output status cell then signs; reason: these are the operations of Definition B.1, and the page fixes no layout. Index cells start at 0, so n, m, b are read by a counting loop in O(n + m + b) steps
--   - reading: "Every execution runs in time polynomial"; "returns such a signing or reports failure" → for every tape ω, including draws outside [0,1]: halting within the time bound, and on status 1 the output is a signing within the bound; reason: (7.14) is pathwise and Theorem C.4 bounds every execution; the scan of equal intervals assigns an out-of-range draw to the last interval
--   - encoding: uniform draws in [0,1) → the uniform on [0,1] of tapeLaw; reason: the two laws agree, differing on a null set
--   - encoding: "polynomial in n, m, b", failure probability → C(n+m+b+2)^K with +2 so the bound is at least C at n = m = 0; the bad event under tapeLaw, an outer measure if not measurable; reason: the strong reading of both
--   - encoding: σ ∈ {−1,1}ⁿ; the empty cases → σ i = 1 ∨ σ i = −1 over Fin n; at n = 0 or m = 0 Lean's log 0 = 0 and x/0 = 0; reason: both clauses then hold with the zero matrix, as Algorithm 3's first line says
-- source:
--   T. Kathuria, A Walk From Free Probability to Matrix Discrepancy I: Matrix Spencer, arXiv:2609.18914 (held file sha256 e1c1ba14…), Theorem 1.1, p.2; Definition B.1, p.74; Algorithm 3, p.78–79; Appendix F, p.90

import Mathlib
import Definitions.Def_FreeSpencer_bound
import Definitions.Def_FreeSpencer_Admissible
import Definitions.Def_FreeSpencer_layout
import Definitions.Def_FreeSpencer_Success
open scoped Matrix Matrix.Norms.L2Operator

namespace FreeSpencer

/-- **Theorem 1.1**: signs with `‖∑ σᵢ Aᵢ‖ ≤ 4000 √(n max{1, 1 + log(2m/n)})` for all real symmetric
contractions, and one randomized real-arithmetic program that returns such a signing or reports failure,
with failure probability at most `2^{-b}` and time polynomial in `n, m, b` on every execution.
Source: Kathuria, A Walk From Free Probability to Matrix Discrepancy I: Matrix Spencer, arXiv:2609.18914 (held file sha256 e1c1ba14…), Theorem 1.1, p.2; Definition B.1, p.74; Appendix F, p.90.

**Formalization Note** The model is the published real RAM restricted by `Admissible`: Definition B.1 without
its eigendecomposition primitive, as Appendix F establishes (p.90). The program, `C` and `K` come before
`n, m, b, A`: "constants independent of the entries of the matrices". Time is `t + 1`, the executed
instructions counted by the machine, on every tape, and soundness holds on every tape; failure is the bad
event under the tape law, an outer measure if the event were not measurable. The uniform draw reads
`[0, 1]` for the paper's `[0, 1)`, the same law. The norm is the `L²` operator norm. At `n = 0` or `m = 0`
both clauses hold with the zero matrix. -/
theorem theorem_1_1 :
    (∀ (n m : ℕ) (A : Fin n → Matrix (Fin m) (Fin m) ℝ), (∀ i, (A i).IsSymm) → (∀ i, ‖A i‖ ≤ 1) →
      ∃ σ : Fin n → ℝ, (∀ i, σ i = 1 ∨ σ i = -1) ∧ ‖∑ i, σ i • A i‖ ≤ bound n m) ∧
    ∃ P : MatMulTimeLP.Program, Admissible P ∧ ∃ C K : ℕ,
      ∀ (n m : ℕ) (A : Fin n → Matrix (Fin m) (Fin m) ℝ), (∀ i, (A i).IsSymm) → (∀ i, ‖A i‖ ≤ 1) →
      ∀ b : ℕ, 1 ≤ b →
        (∀ ω : MatMulTimeLP.Tape, ∃ t : ℕ, MatMulTimeLP.HaltsAt P (layout n m b A) ω t ∧
          t + 1 ≤ C * (n + m + b + 2) ^ K ∧
          (Success P (layout n m b A) ω t n →
            (∀ i, outSigns P (layout n m b A) ω t n i = 1 ∨ outSigns P (layout n m b A) ω t n i = -1) ∧
            ‖∑ i, outSigns P (layout n m b A) ω t n i • A i‖ ≤ bound n m)) ∧
        MatMulTimeLP.tapeLaw {ω | ∃ t : ℕ, MatMulTimeLP.HaltsAt P (layout n m b A) ω t ∧
          ¬ Success P (layout n m b A) ω t n} ≤ (1 / 2 : ENNReal) ^ b := by sorry

end FreeSpencer
