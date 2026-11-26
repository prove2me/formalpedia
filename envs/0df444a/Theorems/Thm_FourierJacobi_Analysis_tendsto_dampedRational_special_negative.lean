-- Prove2me | Theorems.Thm_FourierJacobi_Analysis_tendsto_dampedRational_special_negative
-- name    : FourierJacobi.Analysis.tendsto_dampedRational_special_negative
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:37:36.416574+00:00
-- url     : https://prove2.me/theorems/0fd7abf9-6ce8-4155-a9cd-82e9d9fee354
-- title:
--   Analysis: tendsto damped Rational special negative
-- statement:
--   The Analysis construction uses the tendsto damped Rational special negative property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/RationalLimits.lean#L378-L393
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/RationalLimits.lean#L378-L393

import Definitions.Def_FourierJacobi_Analysis_CoreParameters
import Mathlib.Tactic.FunProp
import Definitions.Def_FourierJacobi_Analysis_RationalLimits
set_option autoImplicit false
noncomputable section
open FourierJacobi FourierJacobi.Analysis
open FourierJacobi.Algebra Filter
open scoped Topology
set_option maxHeartbeats 4000000

theorem FourierJacobi.Analysis.tendsto_dampedRational_special_negative (q : ℝ) (hq : 1 < q) (a b : ℂ)
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    (ha₁ : a ≠ 1) (hb₁ : b ≠ 1) (hab : a ≠ b) (hab₁ : a * b ≠ 1)
    (haM : a ≠ -1) (hbM : b ≠ -1) :
    Tendsto (fun T => ((1 - (-1 : ℂ)) / ((q : ℂ) + 1)) *
      dampedRational (inverseSqrt q) a b (-(inverseSqrt q : ℂ)) T)
      (𝓝[Set.Ioo 0 1] 1)
      (𝓝 (((1 - (-1 : ℂ)) / ((q : ℂ) + 1)) *
        paperE q a b (-(inverseSqrt q : ℂ)))) := by sorry
