-- Prove2me | Theorems.Thm_GlobalTheory_gaussAddValFrac_algebraMap
-- name    : GlobalTheory.gaussAddValFrac_algebraMap
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:40:53.740304+00:00
-- url     : https://prove2.me/theorems/0386a98d-fb17-4967-8e32-ac506cbe617b
-- title:
--   Global Theory: gauss Add Val Frac algebra Map
-- statement:
--   The Global Theory construction uses the gauss Add Val Frac algebra Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/TensorContentEqPolyContentScalarCoeffs.lean#L992-L996
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/TensorContentEqPolyContentScalarCoeffs.lean#L992-L996

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

theorem GlobalTheory.gaussAddValFrac_algebraMap {K Γ σ F : Type*} [Field K]
    [LinearOrderedAddCommGroupWithTop Γ] (v : AddValuation K Γ) [Field F]
    [Algebra (MvPolynomial σ K) F] [IsFractionRing (MvPolynomial σ K) F]
    (f : MvPolynomial σ K) : gaussAddValFrac v σ F (algebraMap _ F f) = gaussAddVal v f := by sorry
