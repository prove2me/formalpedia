-- Prove2me | Theorems.Thm_ImprovedSteinerForest_Main_lemma_8_1
-- name    : ImprovedSteinerForest.Main.lemma_8_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T01:27:30.141926+00:00
-- url     : https://prove2.me/theorems/3ca05d53-2cfa-4eea-b9d4-6bc2a2e2b63c
-- title:
--   Lemma 8.1 — exact coefficient certificate: cost coefficients sum to one, all others nonnegative for every block size, right side ≤ r*, ν < 7/20
-- statement:
--   Apply the 72 positive integer weights of Appendix F, each divided by $10^{14}$, to the rows rounding (8.4), growth (8.5), pair (8.6), the 67 menu rows (8.7) and budget (8.8), size (8.9), with the rational bounds of §8.1 ($\overline a+\eta$ for the cost coefficient, $\overline\lambda_c$ for the error coefficient, $\underline\omega$ for the saving profile). Then:
--
--   - the coefficients of the candidate costs sum to one: $w_g+w_r+\nu=1$;
--   - the coefficients $c_e,c_z,c_h$ of the scalar variables are nonnegative;
--   - every good-block coefficient is nonnegative, $c^G_{n,j}\ge0$ for all $n\ge 2$ and $1\le j\le\lfloor n/2\rfloor$, and every bad-block coefficient is nonnegative, $c^B_n\ge 0$ for all $n\ge2$;
--   - the coefficient on the right-hand side is at most $r^*$:
--   $$2(1+\varepsilon)(w_g+w_r)+\eta w_r+g\nu-2\varepsilon w_b+4w_s\le r^*;$$
--   - the purchase rows have total weight $\nu=33801416789463/10^{14}<7/20$.
--
--   This is the finite certificate behind Lemma 3.4: summing the weighted rows bounds a weighted average of the candidate costs by $r^*\,\mathrm{opt}+\nu(t-g)_+\mathrm{opt}$, and $\nu<7/20$ gives the one-step factor.
--
--   **Formalization Note.** The rows enter through the expanded coefficient formulas of Appendix F.1 ((F.1), (F.2) and the right-hand coefficient), which collect the terms of (8.4)–(8.9) after $\ell_{\mathrm{ref}}=\sum_{n\ge2}(x_n+\bar x_n)$ and $x_n=\sum_j x_{n,j}$; the menu rows' scores $\zeta_i$ and bounds $\beta_i$ are the functions of Appendix D and (7.1)–(7.2) for the row's rule, menu and charge.
--
--   Differences from the source:
--   - encoding: "apply the weights to these rows" → the expanded coefficients `cE, cZ, cH, cG n j, cB n, rhsCoeff` of Appendix F.1 with the rational bounds of §8.1; reason: the paper's own expansion of the weighted rows (checked term by term against (8.4)–(8.9) in MODERATION_NOTES.md).
--   - encoding: "all coefficients of block counts" → `∀ n ≥ 2, ∀ j, 1 ≤ j ≤ n/2, cG n j ≥ 0` and `∀ n ≥ 2, cB n ≥ 0`; reason: good blocks of type (n, j) have `n ≥ 2`, `1 ≤ j ≤ ⌊n/2⌋` (p. 31), bad blocks `n ≥ 2` reference moats.
-- source:
--   Cheshm Jahan, Keshavarz Hedayati, Safari, Shahrezaei, Improved Steiner Forest Approximation via Cut Spaces, STOC 2027 submission (manuscript sha256 b2bf022d…0444), p. 40, Lemma 8.1; pp. 64–67, App. F

import Mathlib
import Definitions.Def_ImprovedSteinerForest_Main_Certificate
open ImprovedSteinerForest.Main.Certificate

namespace ImprovedSteinerForest.Main

/-- Lemma 8.1 (Exact coefficient certificate, p. 40): with the 72 weights of Appendix F (each
numerator divided by `10¹⁴`) applied to the rows (8.4)–(8.9), the candidate-cost coefficients
sum to one (`w_g + w_r + ν = 1`), the coefficients of `e, z, h` and of every good-block count
`x_{n,j}` (`n ≥ 2`, `1 ≤ j ≤ ⌊n/2⌋`) and bad-block count `x̄_n` (`n ≥ 2`) are nonnegative, the
right-hand coefficient is at most `r*`, and the purchase rows have total weight
`ν = 33801416789463/10¹⁴ < 7/20`. -/
theorem lemma_8_1 :
    wg + wr + nu = 1 ∧ 0 ≤ cE ∧ 0 ≤ cZ ∧ 0 ≤ cH ∧
      (∀ n j : ℕ, 2 ≤ n → 1 ≤ j → 2 * j ≤ n → 0 ≤ cG n j) ∧
      (∀ n : ℕ, 2 ≤ n → 0 ≤ cB n) ∧
      rhsCoeff ≤ rStar ∧ nu = 33801416789463 / 10 ^ 14 ∧ nu < 7 / 20 := by sorry

end ImprovedSteinerForest.Main
