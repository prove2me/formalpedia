-- Prove2me | Theorems.Thm_MemSampleNGCA_Main_eq_40
-- name    : MemSampleNGCA.Main.eq_40
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T19:40:44.424199+00:00
-- url     : https://prove2.me/theorems/be366e43-6f9b-419c-8234-b7c7293f293b
-- title:
--   §C.1.1, Eq. (40) — Laurent–Massart: P(Z ≤ n − 2√(nt)) ≤ e^{−t}, P(Z ≥ n + 2√(nt) + 2t) ≤ e^{−t} for Z ∼ χ²_n
-- statement:
--   Let $Z\sim\chi^2_n$ be the sum of the squares of $n\ge1$ independent standard Gaussian variables. For every $t>0$,
--   $$P\big(Z\le n-2\sqrt{nt}\big)\le e^{-t},\qquad P\big(Z\ge n+2\sqrt{nt}+2t\big)\le e^{-t}.$$
--
--   These are the chi-squared tail bounds of Laurent and Massart, which the paper cites. They control both the norm of a Gaussian vector and the norm of its projection onto a low-dimensional subspace, and they enter the proof of Proposition C.4.
--
--   Differences from the source:
--   - encoding: Z ∼ χ²_n → Z = Σ_{i<n} G_i² under the product of n copies of N(0, 1) (Measure.pi); reason: this is the definition of the χ²_n law
--   - reading: χ²_n → n ≥ 1; reason: chi-squared degrees of freedom are positive integers (at n = 0 the first bound would read P(0 ≤ 0) = 1 ≤ e^{−t}); the paper applies (40) only with n = d and n = k ≥ 1
-- source:
--   Pensia, Gupta, Verchand, Sharan, Vedantam, Memory-Sample Tradeoffs in High-Dimensional Statistics, STOC 2027 submission (manuscript sha256 ac94994a…), p. 27 (PDF 29), §C.1.1, Eq. (40), citing Laurent–Massart [LM00, Section 4.1, (4.3)–(4.4)]

import Mathlib
import Definitions.Def_MemSampleNGCA_Main_NGCA

open MeasureTheory
open scoped ENNReal

namespace MemSampleNGCA.Main

/-- §C.1.1, Eq. (40) (p. 27, PDF 29), the Laurent–Massart inequalities: for `Z ∼ χ²_n`
(the sum of squares of `n ≥ 1` independent standard Gaussians) and `t > 0`,
`P(Z ≤ n − 2√(nt)) ≤ e^{−t}` and `P(Z ≥ n + 2√(nt) + 2t) ≤ e^{−t}`. -/
theorem eq_40 (n : ℕ) (hn : 1 ≤ n) (t : ℝ) (ht : 0 < t) :
    (Measure.pi fun _ : Fin n => gamma1)
        {x | ∑ i, x i ^ 2 ≤ (n : ℝ) - 2 * Real.sqrt (n * t)} ≤ ENNReal.ofReal (Real.exp (-t)) ∧
    (Measure.pi fun _ : Fin n => gamma1)
        {x | (n : ℝ) + 2 * Real.sqrt (n * t) + 2 * t ≤ ∑ i, x i ^ 2} ≤
      ENNReal.ofReal (Real.exp (-t)) := by sorry

end MemSampleNGCA.Main
