-- Prove2me | Theorems.Thm_KMeansTaper_coefficients_identities
-- name    : KMeansTaper.coefficients_identities
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T17:04:57.500887+00:00
-- url     : https://prove2.me/theorems/409bb938-ac78-4bd7-adc4-aae93f195266
-- title:
--   Section 2: properties of the coefficients and the identities (1)
-- statement:
--   Let $\kappa>0$ and $x\in[0,1]$, and let $P,A,B=\kappa P,m=A-1-xB$ be the coefficients of Section 2. Then
--
--   1. $A'=B$ and $A''<0$;
--   2. $m\ge0$;
--   3. $0<\kappa P(1)\le B\le\kappa/2$, $|B'|\le\kappa/3$ and $|B''|\le\kappa/4$;
--   4. $A(1)=1+\kappa/e$;
--   5. the identities
--   $$(1+x)A+xB-1=(1+\kappa)x,\qquad A+(2+x)B+xB'=1+\kappa,$$
--   and, for every $y$, with $a=A+B(y-x)$,
--   $$(1+y)a+yB+x(y-x)B'-1=(1+\kappa)y+B(y-x)^2;\quad(1)$$
--   6. $1\le a\le1+\kappa$ for every $y\in[0,1]$.
--
--   These identities turn the time derivative of the potential into the constant $(1+\kappa)+\kappa\Theta$ of SFI.
--
--   **Formalization Note** Derivatives are taken of the coefficients as functions on $\mathbb R$.
--
--   Differences from the source:
--   - encoding: derivatives A′, A″, B′, B″ of functions of x ∈ [0, 1] → deriv of the coefficients defined on ℝ, at x ∈ [0, 1]; reason: the coefficients are smooth on ℝ, so the two-sided derivative at 0 and 1 equals the one-sided one
--   - reading: "Moreover 1 ≤ a ≤ 1 + κ" with the range of y not named → for every y ∈ [0, 1]; reason: SFI uses y ∈ (0, 1]; [0, 1] is the larger range on which the paper's argument works
--   - encoding: e → Real.exp 1; reason: Lean convention; same number
-- source:
--   Zhu, A tight approximation for metric k-means via squared tapered rounding, STOC 2027 submission (manuscript sha256 8b6610229e43dc2441325b120437136afe762dbd6e873f73919fcb6b043fc5a3), Section 2 ("Coefficients"), identities (1), p.3 (PDF p.6)

import Mathlib
import Definitions.Def_KMeansTaper_coefP

namespace KMeansTaper

/-- **Coefficients and identities (1)**, Section 2 ("Coefficients"), p.3 (PDF p.6).

Zhu, *A tight approximation for metric k-means via squared tapered rounding*, STOC 2027
submission (manuscript sha256 8b6610229e43dc2441325b120437136afe762dbd6e873f73919fcb6b043fc5a3).

For `κ > 0` and `x ∈ [0, 1]`: `B = A'`, `A'' < 0`, `m ≥ 0`, `0 < κP(1) ≤ B ≤ κ/2`,
`|B'| ≤ κ/3`, `|B''| ≤ κ/4`, `A(1) = 1 + κ/e`, `(1 + x)A + xB - 1 = (1 + κ)x`,
`A + (2 + x)B + xB' = 1 + κ`, and for every `y`, with `a = A + B(y - x)`,
`(1 + y)a + yB + x(y - x)B' - 1 = (1 + κ)y + B(y - x)²`; moreover `1 ≤ a ≤ 1 + κ` for
`y ∈ [0, 1]`.

**Formalization Note.** The coefficients are defined on all of `ℝ` and the derivatives are
`deriv` of these functions of `x` (smooth, so the two-sided derivative at `x = 0, 1` is the
one-sided one); `e` is `Real.exp 1`. -/
theorem coefficients_identities (κ : ℝ) (hκ : 0 < κ) (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    deriv (coefA κ) x = coefB κ x ∧
    deriv (deriv (coefA κ)) x < 0 ∧
    0 ≤ coefM κ x ∧
    (0 < κ * coefP 1 ∧ κ * coefP 1 ≤ coefB κ x ∧ coefB κ x ≤ κ / 2) ∧
    |deriv (coefB κ) x| ≤ κ / 3 ∧
    |deriv (deriv (coefB κ)) x| ≤ κ / 4 ∧
    coefA κ 1 = 1 + κ / Real.exp 1 ∧
    (1 + x) * coefA κ x + x * coefB κ x - 1 = (1 + κ) * x ∧
    coefA κ x + (2 + x) * coefB κ x + x * deriv (coefB κ) x = 1 + κ ∧
    (∀ y : ℝ, (1 + y) * (coefA κ x + coefB κ x * (y - x)) + y * coefB κ x
        + x * (y - x) * deriv (coefB κ) x - 1 = (1 + κ) * y + coefB κ x * (y - x) ^ 2) ∧
    (∀ y ∈ Set.Icc (0 : ℝ) 1,
        1 ≤ coefA κ x + coefB κ x * (y - x) ∧ coefA κ x + coefB κ x * (y - x) ≤ 1 + κ) := by sorry

end KMeansTaper
