-- Prove2me | Theorems.Thm_MatMulDS_Supplement_theorem_8_4
-- name    : MatMulDS.Supplement.theorem_8_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-15T20:18:27.339555+00:00
-- url     : https://prove2.me/theorems/53817741-39f5-4488-928f-04f725eab58d
-- title:
--   Theorem 8.4 — fully sparse matrix multiplication in $O(\mu^{4/3-\xi})$, $\xi=2\beta/(9+25\beta)$
-- statement:
--   Let $\beta\le1/50$ be an admissible saving, and set $\xi=2\beta/(9+25\beta)$. There is a deterministic algorithm that, given matrices $A$ and $B$ with entries in $\{0,\dots,\mu^{O(1)}\}$ in sparse representation, computes $AB$ in sparse representation in
--   $$O(\mu^{4/3-\xi})=O(\mu^{1.3332742})$$
--   time, where $\mu=\mathrm{nnz}(A)+\mathrm{nnz}(B)+\mathrm{nnz}(AB)$.
--
--   The exponent $4/3$ was a barrier for output-sensitive sparse products; the theorem also gives transitive closure and join-project queries below it.
--
--   Differences from the source:
--   - generalization: an algorithm on the word RAM → one word program for every word size $w\ge K\lceil\log_2(a+b+c+\mu+1)\rceil+K$, all steps counted; reason: $\Theta(\log)$ of the numbers in the input; it specializes to each such word size
--   - encoding: matrices with arbitrary dimensions; entries in $\{0,\dots,\mu^{O(1)}\}$ → any $a,b,c$; for every $c_0$ entries at most $\mu^{c_0}$, with the program chosen after $c_0$; reason: the meaning of $\mu^{O(1)}$
--   - encoding: sparse representation of input and output → `sparseWords` (triples in any order) and `SparseOut` (all nonzero entries, each once); reason: footnote 10
--   - encoding: $O(\mu^{4/3-\xi})$ → $C(\mu+1)^{4/3-\xi}$ steps; reason: the same for $\mu\ge1$; the $+1$ only covers $A=B=0$
--   - encoding: the numerical form $O(\mu^{1.3332742})$ → a separate conjunct, the inequality at $\beta=0.0002666$; reason: the source evaluates its bound at the admissible saving of Theorem 7.4
-- source:
--   J. Alman, J. Nogler, V. Vassilevska Williams, Subquadratic Time Matrix Multiplication Data Structures Beyond the Dual Exponent, with Applications, STOC 2027 submission (held file sha256 6c5a1c16…), Theorem 8.4, p.53 (PDF p.55)

import Mathlib
import Definitions.Def_MatMulDS_Supplement_sparseWords

set_option autoImplicit false

open MatroidSensOracle MatMulDS

namespace MatMulDS.Supplement

/-- **Theorem 8.4, p.53** (Alman, Nogler, Vassilevska Williams, STOC 2027 submission, held file sha256 6c5a1c16…). Let
`β ≤ 1/50` be an admissible saving, and set `ξ = 2β/(9 + 25β)`. There is a deterministic algorithm that, given matrices `A` and `B`
with entries in `{0, …, µ^{O(1)}}` in sparse representation, computes `AB` in sparse representation in
`O(µ^{4/3−ξ}) = O(µ^{1.3332742})` time, where `µ = nnz(A) + nnz(B) + nnz(AB)`.

**Formalization Note.**
* The algorithm is a word program of the published machine (deterministic word RAM), all steps counted, for every word size
  `w ≥ K⌈log₂(a + b + c + µ + 1)⌉ + K` (`Θ(log)` of the input's numbers; the dimensions `a, b, c` are arbitrary).
* `µ^{O(1)}`: for every `c₀`, entries at most `µ^{c₀}`, with the program and constants chosen after `c₀`. `O(µ^x)` is
  `C (µ + 1)^x`, the same for `µ ≥ 1`; the `+ 1` only covers `A = B = 0`.
* The numerical form is the instance `β = 0.0002666` (Theorem 7.4), stated as the last conjunct. -/
theorem theorem_8_4 (β : ℝ) (hβ : AdmissibleSaving β) (hβ50 : β ≤ 1 / 50) :
    (∀ c₀ : ℕ, ∃ (P : List AInstr) (K : ℕ) (C : ℝ), 0 < C ∧ IsWordProgram P ∧
      ∀ (a b c : ℕ) (A : Matrix (Fin a) (Fin b) ℕ) (B : Matrix (Fin b) (Fin c) ℕ)
        (esA : List (Fin a × Fin b)) (esB : List (Fin b × Fin c)),
        IsSparseRep A esA → IsSparseRep B esB →
        (∀ i j, A i j ≤ (esA.length + esB.length + nnz (A * B)) ^ c₀) →
        (∀ i j, B i j ≤ (esA.length + esB.length + nnz (A * B)) ^ c₀) →
        ∀ w : ℕ, K * Nat.clog 2 (a + b + c + (esA.length + esB.length + nnz (A * B)) + 1) + K ≤ w →
        ∃ st : ℤ → BitVec w,
          wordRun P w (sparseWords A B esA esB)
            ⌈C * (((esA.length + esB.length + nnz (A * B) : ℕ) : ℝ) + 1) ^ ((4 : ℝ) / 3 - 2 * β / (9 + 25 * β))⌉₊ =
              some st ∧
          SparseOut (A * B) st) ∧
    (4 : ℝ) / 3 - 2 * 0.0002666 / (9 + 25 * 0.0002666) ≤ 1.3332742 := by sorry

end MatMulDS.Supplement
