-- Prove2me | Theorems.Thm_FourierJacobi_Analysis_finiteRegular_interior
-- name    : FourierJacobi.Analysis.finiteRegular_interior
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:23:52.007241+00:00
-- url     : https://prove2.me/theorems/36869da9-30ba-435a-b505-7d2620efb814
-- title:
--   Analysis: finite Regular interior
-- statement:
--   The Analysis construction uses the finite Regular interior property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/CoreParameters.lean#L134-L167
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/CoreParameters.lean#L134-L167

import Definitions.Def_FourierJacobi_Algebra_UnitaryFinite
import Definitions.Def_FourierJacobi_Analysis_ValuationSeries
import Definitions.Def_FourierJacobi_Analysis_CoreParameters
set_option autoImplicit false
noncomputable section
open FourierJacobi FourierJacobi.Analysis
open FourierJacobi.Algebra

theorem FourierJacobi.Analysis.finiteRegular_interior {t : ℝ} {a b d : ℂ}
    (ht₀ : 0 < t) (ht₁ : t < 1) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    (hdlo : t < ‖d‖) (hdhi : ‖d‖ ≤ 1)
    (ha₁ : a ≠ 1) (hb₁ : b ≠ 1) (hab : a ≠ b) (hab₁ : a * b ≠ 1) :
    FiniteRegular (t : ℂ) a b d := by sorry
