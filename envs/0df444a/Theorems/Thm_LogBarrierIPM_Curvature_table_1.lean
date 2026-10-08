-- Prove2me | Theorems.Thm_LogBarrierIPM_Curvature_table_1
-- name    : LogBarrierIPM.Curvature.table_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T01:22:37.772446+00:00
-- url     : https://prove2.me/theorems/3a23c5f0-1851-4e8c-8868-8d726cf75433
-- title:
--   Table 1 — coordinates of the primal tropical central path of $\mathbf{LW}_r$ at $\lambda=(4k+2c)/2^j$
-- statement:
--   Let $x^\lambda,w^\lambda$ be the primal tropical central path of $\mathbf{LW}_r$, given by the recursions of Propositions 20 and 21. Let $1\le j<r$ and let $k\in\{0,2,\dots,2^{j-1}-2\}$ (an even integer with $k+2\le 2^{j-1}$; there is none for $j=1$). At the five parameters $\lambda=\frac{4k}{2^j},\frac{4k+2}{2^j},\frac{4k+4}{2^j},\frac{4k+6}{2^j},\frac{4k+8}{2^j}$ the coordinates are
--
--   | $\lambda$ | $\frac{4k}{2^j}$ | $\frac{4k+2}{2^j}$ | $\frac{4k+4}{2^j}$ | $\frac{4k+6}{2^j}$ | $\frac{4k+8}{2^j}$ |
--   |---|---|---|---|---|---|
--   | $x_{2j+1}$ | $j+\frac{2k}{2^j}$ | $j+\frac{2k+2}{2^j}$ | $j+\frac{2k+2}{2^j}$ | $j+\frac{2k+4}{2^j}$ | $j+\frac{2k+4}{2^j}$ |
--   | $x_{2j+2}$ | $j+\frac{2k+1}{2^j}$ | $j+\frac{2k+1}{2^j}$ | $j+\frac{2k+3}{2^j}$ | $j+\frac{2k+3}{2^j}$ | $j+\frac{2k+5}{2^j}$ |
--   | $w_{3j}$ | $j+\frac{2k}{2^j}$ | $j+\frac{2k+2}{2^j}$ | $j+\frac{2k+4}{2^j}$ | $j+\frac{2k+4}{2^j}$ | $j+\frac{2k+4}{2^j}$ |
--   | $w_{3j+1}$ | $j+\frac{2k+2}{2^j}$ | $j+\frac{2k+2}{2^j}$ | $j+\frac{2k+2}{2^j}$ | $j+\frac{2k+4}{2^j}$ | $j+\frac{2k+6}{2^j}$ |
--   | $w_{3j+2}$ | $j+\frac{2k+1}{2^j}$ | $j+\frac{2k+1}{2^j}$ | $j+\frac{2k+3}{2^j}$ | $j+\frac{2k+3}{2^j}$ | $j+\frac{2k+5}{2^j}$ |
--
--   These values are what the proof of Theorem 25 reads off to locate the largest coordinate of the tropical central path.
--
--   **Formalization Note** The table is stated for the explicit tropical central path of the definition `TropicalCentralPathLW` (the formulas of Propositions 20 and 21), with the paper's 1-based coordinate indices. Each of the 25 cells is one equality $\text{coordinate}(\lambda)=j+(2k+a)/2^j$.
-- source:
--   Allamigeon, Benchimol, Gaubert, Joswig, Log-Barrier Interior Point Methods Are Not Strongly Polynomial, arXiv:1708.01544v2, p. 21, Table 1

import Mathlib
import Definitions.Def_LogBarrierIPM_Curvature_TropicalCentralPathLW

namespace LogBarrierIPM.Curvature

/-- Table 1 (p. 21). For `1 ≤ j < r` and `k = 0, 2, …, 2^{j−1} − 2`, the coordinates
`x_{2j+1}, x_{2j+2}, w_{3j}, w_{3j+1}, w_{3j+2}` of the primal tropical central path of `LW_r` at
`λ = (4k + 2c)/2^j`, `c = 0, …, 4`, are the printed values `j + (2k + a)/2^j`. -/
theorem table_1 (r j k : ℕ) (hj : 1 ≤ j) (hjr : j < r) (hk : Even k) (hk2 : k + 2 ≤ 2 ^ (j - 1)) :
    let L : ℕ → ℝ := fun a => (4 * (k : ℝ) + a) / 2 ^ j
    let T : ℕ → ℝ := fun a => (j : ℝ) + (2 * (k : ℝ) + a) / 2 ^ j
    -- row x_{2j+1}
    (tropX (L 0) (2 * j + 1) = T 0 ∧ tropX (L 2) (2 * j + 1) = T 2 ∧
      tropX (L 4) (2 * j + 1) = T 2 ∧ tropX (L 6) (2 * j + 1) = T 4 ∧
      tropX (L 8) (2 * j + 1) = T 4) ∧
    -- row x_{2j+2}
    (tropX (L 0) (2 * j + 2) = T 1 ∧ tropX (L 2) (2 * j + 2) = T 1 ∧
      tropX (L 4) (2 * j + 2) = T 3 ∧ tropX (L 6) (2 * j + 2) = T 3 ∧
      tropX (L 8) (2 * j + 2) = T 5) ∧
    -- row w_{3j}
    (tropW (L 0) (3 * j) = T 0 ∧ tropW (L 2) (3 * j) = T 2 ∧
      tropW (L 4) (3 * j) = T 4 ∧ tropW (L 6) (3 * j) = T 4 ∧
      tropW (L 8) (3 * j) = T 4) ∧
    -- row w_{3j+1}
    (tropW (L 0) (3 * j + 1) = T 2 ∧ tropW (L 2) (3 * j + 1) = T 2 ∧
      tropW (L 4) (3 * j + 1) = T 2 ∧ tropW (L 6) (3 * j + 1) = T 4 ∧
      tropW (L 8) (3 * j + 1) = T 6) ∧
    -- row w_{3j+2}
    (tropW (L 0) (3 * j + 2) = T 1 ∧ tropW (L 2) (3 * j + 2) = T 1 ∧
      tropW (L 4) (3 * j + 2) = T 3 ∧ tropW (L 6) (3 * j + 2) = T 3 ∧
      tropW (L 8) (3 * j + 2) = T 5) := by sorry

end LogBarrierIPM.Curvature
