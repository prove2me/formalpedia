-- Prove2me | Theorems.Thm_OAI_TwoPointCorrelations_MRTWeakHurwitzGrowthInput_riesz_far_tail
-- name    : OAI.TwoPointCorrelations.MRTWeakHurwitzGrowthInput.riesz_far_tail
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T01:15:11.994158+00:00
-- url     : https://prove2.me/theorems/883f7514-006a-4533-a01e-5a0f7097e6da
-- title:
--   Under the weak Hurwitz growth input, the far tails of the Riesz contour integral are O(x^b T^{−3/2})
-- statement:
--   Assume `MRTWeakHurwitzGrowthInput`. Then there are $C>0$ and $T_0>0$ such that for all reals $x>0$, $b>1$, $T\ge T_0$ and $|u|\le T/2$,
--
--   $$\Big|\,i\!\int_{\mathbb R}R(b+it)\,dt-i\!\int_{-T}^{T}R(b+it)\,dt\Big|\le C\,x^b\,T^{-3/2},$$
--
--   where $R(s)$ = `mrtZetaRieszIntegrand x u s` $=-\frac{\zeta'}{\zeta}(s+iu)\cdot\kappa(x,s)$ with the bundle's Riesz kernel $\kappa$ = `mrtRieszKernel`, and the two integrals are `VerticalIntegral R b` and `VIntegral R b (-T) T`.
-- source:
--   OpenAI, Ordinary two-point correlations of multiplicative functions, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/main/preprints/Ordinary-two-point-correlations-of-multiplicative-functions-September-24-2026/final.pdf; Lean: lean/OAI/NumberTheory/TwoPoint, Apache License 2.0); Lean declaration `OAI.TwoPointCorrelations.MRTWeakHurwitzGrowthInput.riesz_far_tail`

import Mathlib
import Definitions.Def_OAIChowlaTwoPointDefs

namespace OAI.TwoPointCorrelations

open Complex
open Set
open MeasureTheory
open _root_.Erdos970
open OAI.Erdos970

theorem MRTWeakHurwitzGrowthInput.riesz_far_tail (h : MRTWeakHurwitzGrowthInput) :
    ∃ C T₀ : ℝ, 0 < C ∧ 0 < T₀ ∧ ∀ x b T u : ℝ,
      0 < x → 1 < b → T₀ ≤ T → |u| ≤ T / 2 →
        ‖VerticalIntegral (mrtZetaRieszIntegrand x u) b -
          VIntegral (mrtZetaRieszIntegrand x u) b (-T) T‖ ≤
            C * x ^ b * T ^ (-(3 / 2 : ℝ)) := by
  sorry

end OAI.TwoPointCorrelations
