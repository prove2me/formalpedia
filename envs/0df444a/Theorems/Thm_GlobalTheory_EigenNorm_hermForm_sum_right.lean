-- Prove2me | Theorems.Thm_GlobalTheory_EigenNorm_hermForm_sum_right
-- name    : GlobalTheory.EigenNorm.hermForm_sum_right
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T12:56:35.863087+00:00
-- url     : https://prove2.me/theorems/81808ad6-b12a-4638-8ebe-f3737d0259d4
-- title:
--   Eigen Norm: herm Form sum right
-- statement:
--   The Eigen Norm construction uses the herm Form sum right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/EqZeroOfSumEmbeddingMul.lean#L40-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/EqZeroOfSumEmbeddingMul.lean#L40-L42

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_EqZeroOfSumEmbeddingMul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.EigenNorm
variable {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ)

theorem GlobalTheory.EigenNorm.hermForm_sum_right {κ : Type*} (s : Finset κ) (z : Fin g → ℂ) (w : κ → Fin g → ℂ) :
    hermForm Hm z (∑ i ∈ s, w i) = ∑ i ∈ s, hermForm Hm z (w i) := by sorry
