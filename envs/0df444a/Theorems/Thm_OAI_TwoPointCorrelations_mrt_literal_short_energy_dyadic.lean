-- Prove2me | Theorems.Thm_OAI_TwoPointCorrelations_mrt_literal_short_energy_dyadic
-- name    : OAI.TwoPointCorrelations.mrt_literal_short_energy_dyadic
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T01:13:29.745805+00:00
-- url     : https://prove2.me/theorems/7cbc2330-06c1-461e-9787-59eaf4b24d04
-- title:
--   Short-interval sums in mean square are controlled by kernel-weighted mean squares of dyadic polynomials
-- statement:
--   Let $b:\mathbb N\to\mathbb C$ and naturals $0<H\le N$. Then
--
--   $$\frac{1}{NH^2}\int_N^{2N}\Big|\sum_{\lfloor x\rfloor<n\le\lfloor x+H\rfloor}b(n)\Big|^2dx\le\frac{139968}{2\pi}\Big(\int_{\mathbb R}k_{N/H}(t)\,|D_N(t)|^2dt+\int_{\mathbb R}k_{N/H}(t)\,|D_{2N}(t)|^2dt\Big),$$
--
--   where $k_T(t)=\min(1,T^2/(1+t^2))$ (`mrtShortKernel`), $D_M(t)=\sum_{M<n\le2M}\frac{b(n)}nn^{-it}$ (`mrtDyadicPolynomial`), and the inner sum is `shortExponentialSum b H 0 x`. Integrals of non-integrable functions are $0$ by Lean's convention.
-- source:
--   OpenAI, Ordinary two-point correlations of multiplicative functions, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/main/preprints/Ordinary-two-point-correlations-of-multiplicative-functions-September-24-2026/final.pdf; Lean: lean/OAI/NumberTheory/TwoPoint, Apache License 2.0); Lean declaration `OAI.TwoPointCorrelations.mrt_literal_short_energy_dyadic`

import Mathlib
import Definitions.Def_OAIChowlaTwoPointDefs

namespace OAI.TwoPointCorrelations

open MeasureTheory
open Finset
open Set
open scoped Classical

theorem mrt_literal_short_energy_dyadic (b : ℕ → ℂ) {N H : ℕ}
    (hH : 0 < H) (hHN : H ≤ N) :
    (∫ x in (N:ℝ)..(2*N), ‖shortExponentialSum b H 0 x‖^2) /
        ((N:ℝ)*(H:ℝ)^2) ≤
      (139968/(2*Real.pi)) *
        ((∫ t : ℝ, mrtShortKernel ((N:ℝ)/H) t * ‖mrtDyadicPolynomial b N t‖^2) +
          ∫ t : ℝ, mrtShortKernel ((N:ℝ)/H) t * ‖mrtDyadicPolynomial b (2*N) t‖^2) := by
  sorry

end OAI.TwoPointCorrelations
