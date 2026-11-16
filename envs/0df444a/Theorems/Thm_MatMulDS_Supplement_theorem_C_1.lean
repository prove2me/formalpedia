-- Prove2me | Theorems.Thm_MatMulDS_Supplement_theorem_C_1
-- name    : MatMulDS.Supplement.theorem_C_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-15T20:23:56.947202+00:00
-- url     : https://prove2.me/theorems/2e098e97-3cb3-43e0-bdaa-4e220f2c1fe9
-- title:
--   Theorem C.1 — minimum witness product in $\tilde O(T_{\mathrm{coarse}}+T_{\mathrm{refine}}+T_{\mathrm{scan}})$
-- statement:
--   Let $\beta$ be an admissible saving. There is a deterministic algorithm that, given $A,B\in\{0,1\}^{n\times n}$ in dense representation and integers $0\le\nu\le\lambda$ with $2^\lambda\le n$, computes the minimum witness product of $A$ and $B$ and runs in time $\tilde O(T_{\mathrm{coarse}}+T_{\mathrm{refine}}+T_{\mathrm{scan}})$, where
--   $$T_{\mathrm{coarse}}=\frac{n}{2^\lambda}\,\mathrm{MM}(n,2^\lambda,n),\quad T_{\mathrm{refine}}=\Big(\frac{n}{2^\nu}+\sqrt n\Big)n^{2-\beta}+\Big(1+\frac{2^\lambda}{\sqrt n}\Big)n^{5/2-\beta},\quad T_{\mathrm{scan}}=n^2\,2^\nu.$$
--
--   Choosing $\nu$ and $\lambda$ gives Theorem 8.5.
--
--   Differences from the source:
--   - generalization: an algorithm on the word RAM with $\Theta(\log n)$-bit words → one word program of the mission's machine for every word size $w\ge K\lceil\log_2(n+1)\rceil+K$, all steps counted; reason: it specializes to each word size above the threshold and cannot exploit a huge word
--   - encoding: input and output → the words of $A,B$ (`boolWords`), then $\nu,\lambda$; word cell $in+j$ holds the minimum witness ($0$-based) or $-1$; reason: a layout
--   - encoding: $\tilde O$; $\mathrm{MM}$ → $C(\log n+1)^c$ with $C,c$ fixed before $n,\nu,\lambda$; the published `MM` over $\mathbb Q$; reason: polylogarithmic factors; the paper's MM is over characteristic zero
-- source:
--   J. Alman, J. Nogler, V. Vassilevska Williams, Subquadratic Time Matrix Multiplication Data Structures Beyond the Dual Exponent, with Applications, STOC 2027 submission (held file sha256 6c5a1c16…), Theorem C.1, p.86 (PDF p.88)

import Mathlib
import Definitions.Def_MatMulDS_MM
import Definitions.Def_MatMulDS_Supplement_AdmissibleSaving
import Definitions.Def_MatMulDS_Supplement_minWitness

set_option autoImplicit false

open MatroidSensOracle MatMulDS

namespace MatMulDS.Supplement

/-- **Theorem C.1, p.86** (Alman, Nogler, Vassilevska Williams, STOC 2027 submission, held file sha256 6c5a1c16…). Let `β` be an
admissible saving. There is a deterministic algorithm that, given `A, B ∈ {0, 1}^{n×n}` in dense representation and integers
`0 ≤ ν ≤ λ` with `2^λ ≤ n`, computes the minimum witness product of `A` and `B` and runs in time `Õ(T_coarse + T_refine + T_scan)`,
where `T_coarse = (n/2^λ) MM(n, 2^λ, n)`, `T_refine = (n/2^ν + √n) n^{2−β} + (1 + 2^λ/√n) n^{5/2−β}` and `T_scan = n² 2^ν`.

**Formalization Note.**
* The algorithm is a word program of the published machine (deterministic word RAM), all steps counted, for every word size
  `w ≥ K⌈log₂(n+1)⌉ + K`. Input words: those of `A, B` (`boolWords`), then `ν, λ`. Output: word cell `i n + j` holds the minimum
  witness of `(i, j)` (0-based), or `−1` for `∞`.
* `Õ(X)` is `C (log n + 1)^c X` with `C, c` fixed before `n, ν, λ`. `MM` is the published `MM` over `ℚ` (characteristic zero). -/
theorem theorem_C_1 (β : ℝ) (hβ : AdmissibleSaving β) :
    ∃ (P : List AInstr) (K c : ℕ) (C : ℝ), 0 < C ∧ IsWordProgram P ∧
      ∀ (n ν lam : ℕ), ν ≤ lam → 2 ^ lam ≤ n →
      ∀ (A B : Matrix (Fin n) (Fin n) Bool) (w : ℕ), K * Nat.clog 2 (n + 1) + K ≤ w →
        ∃ st : ℤ → BitVec w,
          wordRun P w (boolWords A B ++ [(ν : ℤ), (lam : ℤ)])
            ⌈C * (Real.log n + 1) ^ c *
              ((n : ℝ) / 2 ^ lam * (MM ℚ n (2 ^ lam) n : ℝ) +
               (((n : ℝ) / 2 ^ ν + Real.sqrt n) * (n : ℝ) ^ (2 - β) +
                 (1 + (2 : ℝ) ^ lam / Real.sqrt n) * (n : ℝ) ^ ((5 : ℝ) / 2 - β)) +
               (n : ℝ) ^ 2 * 2 ^ ν)⌉₊ = some st ∧
          ∀ i j : Fin n, (st ((i : ℤ) * n + (j : ℕ))).toInt = witnessCode (minWitness A B i j) := by sorry

end MatMulDS.Supplement
