-- Prove2me | Theorems.Thm_GlobalTheory_finite_gaussVal_ne_one
-- name    : GlobalTheory.finite_gaussVal_ne_one
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T12:46:06.840706+00:00
-- url     : https://prove2.me/theorems/6d5edb02-0cb1-43a0-aae4-65a6fcdf2470
-- title:
--   Global Theory: finite gauss Val ne one
-- statement:
--   The Global Theory construction uses the finite gauss Val ne one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/TensorContentEqPolyContentScalarCoeffs.lean#L998-L1012
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/TensorContentEqPolyContentScalarCoeffs.lean#L998-L1012

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_TensorContentEqPolyContentScalarCoeffs
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
noncomputable section
open scoped NNReal TensorProduct
open MvPolynomial Module IsDedekindDomain

theorem GlobalTheory.finite_gaussVal_ne_one {O K σ : Type*} [CommRing O] [IsDedekindDomain O] [Field K]
    [Algebra O K] [IsFractionRing O K] {f : MvPolynomial σ K} (hf : f ≠ 0) :
    {p : HeightOneSpectrum O | gaussVal (p.valuation K) f ≠ 1}.Finite := by sorry
