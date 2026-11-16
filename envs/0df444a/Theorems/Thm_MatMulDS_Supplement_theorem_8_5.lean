-- Prove2me | Theorems.Thm_MatMulDS_Supplement_theorem_8_5
-- name    : MatMulDS.Supplement.theorem_8_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-15T20:19:08.677314+00:00
-- url     : https://prove2.me/theorems/3569bad5-54fc-4817-94d8-438092a23368
-- title:
--   Theorem 8.5 — minimum witness product in $O(n^{5/2-\xi})$, $\xi=\beta(1-\beta)/2$
-- statement:
--   Let $\beta$ be an admissible saving, and set $\xi=\beta(1-\beta)/2$. There is a deterministic algorithm that, given $A,B\in\{0,1\}^{n\times n}$ in dense representation, computes their minimum witness product in
--   $$O(n^{5/2-\xi})=O(n^{2.4998668})$$
--   time.
--
--   This breaks the $n^{5/2}$ barrier for the minimum witness product, and with it for all-pairs bottleneck paths in vertex-weighted graphs (Corollary 8.6).
--
--   Differences from the source:
--   - generalization: an algorithm on the word RAM with $\Theta(\log n)$-bit words → one word program of the mission's machine for every word size $w\ge K\lceil\log_2(n+1)\rceil+K$, all steps counted; reason: it specializes to each word size above the threshold and cannot exploit a huge word
--   - encoding: input and output → words $n$, then $A$, $B$ row-major as $0/1$; word cell $in+j$ holds the minimum witness ($0$-based) or $-1$ for $\infty$; reason: a layout on the machine
--   - encoding: $O(\cdot)$ → $C\cdot$ with $C$ fixed before the sizes, inside a ceiling as a step budget; reason: the meaning of $O$ for one fixed algorithm
--   - encoding: the numerical form $O(n^{2.4998668})$ → a separate conjunct, the inequality at $\beta=0.0002666$; reason: the source evaluates its bound at the admissible saving of Theorem 7.4
-- source:
--   J. Alman, J. Nogler, V. Vassilevska Williams, Subquadratic Time Matrix Multiplication Data Structures Beyond the Dual Exponent, with Applications, STOC 2027 submission (held file sha256 6c5a1c16…), Theorem 8.5, p.53 (PDF p.55)

import Mathlib
import Definitions.Def_MatMulDS_Supplement_AdmissibleSaving
import Definitions.Def_MatMulDS_Supplement_minWitness

set_option autoImplicit false

open MatroidSensOracle MatMulDS

namespace MatMulDS.Supplement

/-- **Theorem 8.5, p.53** (Alman, Nogler, Vassilevska Williams, STOC 2027 submission, held file sha256 6c5a1c16…). Let `β` be an
admissible saving, and set `ξ = β(1 − β)/2`. There is a deterministic algorithm that, given `A, B ∈ {0, 1}^{n×n}` in dense
representation, computes their minimum witness product in `O(n^{5/2−ξ}) = O(n^{2.4998668})` time.

**Formalization Note.**
* The algorithm is a word program of the published machine (deterministic word RAM), all steps counted, for every word size
  `w ≥ K⌈log₂(n+1)⌉ + K`. Input words: `n`, then `A` and `B` in row-major order as `0`/`1`. Output: word cell `i n + j` holds the
  minimum witness of `(i, j)` (0-based), or `−1` for `∞`.
* The numerical form is the instance `β = 0.0002666`, stated as the last conjunct. -/
theorem theorem_8_5 (β : ℝ) (hβ : AdmissibleSaving β) :
    (∃ (P : List AInstr) (K : ℕ) (C : ℝ), 0 < C ∧ IsWordProgram P ∧
      ∀ (n : ℕ), 1 ≤ n → ∀ (A B : Matrix (Fin n) (Fin n) Bool) (w : ℕ), K * Nat.clog 2 (n + 1) + K ≤ w →
        ∃ st : ℤ → BitVec w,
          wordRun P w (boolWords A B) ⌈C * (n : ℝ) ^ ((5 : ℝ) / 2 - β * (1 - β) / 2)⌉₊ = some st ∧
          ∀ i j : Fin n, (st ((i : ℤ) * n + (j : ℕ))).toInt = witnessCode (minWitness A B i j)) ∧
    (5 : ℝ) / 2 - 0.0002666 * (1 - 0.0002666) / 2 ≤ 2.4998668 := by sorry

end MatMulDS.Supplement
