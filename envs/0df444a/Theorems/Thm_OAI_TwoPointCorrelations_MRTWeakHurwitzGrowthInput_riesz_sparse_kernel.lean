-- Prove2me | Theorems.Thm_OAI_TwoPointCorrelations_MRTWeakHurwitzGrowthInput_riesz_sparse_kernel
-- name    : OAI.TwoPointCorrelations.MRTWeakHurwitzGrowthInput.riesz_sparse_kernel
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T01:12:37.660524+00:00
-- url     : https://prove2.me/theorems/dcad4834-ea0a-48cf-bf75-07d4a3b6c019
-- title:
--   Under the weak Hurwitz growth input, the Riesz-weighted von Mangoldt polynomial decays like 1/(1+u²)
-- statement:
--   Assume `MRTWeakHurwitzGrowthInput`. Then there are $C>0$ and $L_0$ such that for all $L\ge\max(L_0,1)$, $Y\ge2$ and real $u$ with $|u|\le2e^L$,
--
--   $$\Big|\sum_{1\le n\le4Y}w_Y(n)\Lambda(n)\,n^{-iu}\Big|\le\frac{CY}{1+u^2}+CY\,e^{-\log Y/L^{3/4}}L^2,$$
--
--   where $w_Y(n)=4\max(1-\frac n{4Y},0)^2$ (`mrtRieszPrimeWeight`), $\Lambda$ is the von Mangoldt function and the sum is over `mrtRieszPrimeSupport Y` $=\{1,\dots,\lfloor4Y\rfloor\}$.
-- source:
--   OpenAI, Ordinary two-point correlations of multiplicative functions, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/main/preprints/Ordinary-two-point-correlations-of-multiplicative-functions-September-24-2026/final.pdf; Lean: lean/OAI/NumberTheory/TwoPoint, Apache License 2.0); Lean declaration `OAI.TwoPointCorrelations.MRTWeakHurwitzGrowthInput.riesz_sparse_kernel`

import Mathlib
import Definitions.Def_OAIChowlaTwoPointDefs

namespace OAI.TwoPointCorrelations

open Complex
open Filter
open Set
open _root_.Erdos970
open OAI.Erdos970
open scoped Topology

theorem MRTWeakHurwitzGrowthInput.riesz_sparse_kernel (h : MRTWeakHurwitzGrowthInput) :
    ∃ C L₀ : ℝ, 0 < C ∧ ∀ L Y : ℝ, L₀ ≤ L → 1 ≤ L → 2 ≤ Y →
      ∀ u : ℝ, |u| ≤ 2 * Real.exp L →
      ‖mrtExponentialPolynomial (mrtRieszPrimeSupport Y)
        (fun n => (mrtRieszPrimeWeight Y n * ArithmeticFunction.vonMangoldt n : ℝ))
        (fun n => -Real.log (n : ℝ)) u‖ ≤
          C * Y / (1 + u ^ 2) + C * Y * Real.exp (-Real.log Y / L ^ (3 / 4 : ℝ)) * L ^ 2 := by
  sorry

end OAI.TwoPointCorrelations
