-- Prove2me | Theorems.Thm_GlobalTheory_gaussVal_lt_one_iff_map_residue
-- name    : GlobalTheory.gaussVal_lt_one_iff_map_residue
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T22:53:59.474892+00:00
-- url     : https://prove2.me/theorems/244ad712-6105-401e-857a-2aeff825a46f
-- title:
--   Global Theory: gauss Val lt one iff map residue
-- statement:
--   The Global Theory construction uses the gauss Val lt one iff map residue property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/TensorContentEqPolyContentScalarCoeffs.lean#L375-L382
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/TensorContentEqPolyContentScalarCoeffs.lean#L375-L382

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
open MvPolynomial
variable {K Γ₀ σ τ : Type*} [Field K]
variable [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation K Γ₀)

theorem GlobalTheory.gaussVal_lt_one_iff_map_residue {O : Type*} [CommRing O] [IsLocalRing O] [Algebra O K]
    (hO : v.Integers O) (g : MvPolynomial σ O) :
    gaussVal v (map (algebraMap O K) g) < 1 ↔ map (IsLocalRing.residue O) g = 0 := by sorry
