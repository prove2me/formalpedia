-- Prove2me | Theorems.Thm_GlobalTheory_EigenNorm_hermForm_sum_left
-- name    : GlobalTheory.EigenNorm.hermForm_sum_left
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T12:56:34.77481+00:00
-- url     : https://prove2.me/theorems/4b15e744-1da2-4f3d-858c-65a029338bb4
-- title:
--   Eigen Norm: herm Form sum left
-- statement:
--   The Eigen Norm construction uses the herm Form sum left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/EqZeroOfSumEmbeddingMul.lean#L36-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/EqZeroOfSumEmbeddingMul.lean#L36-L38

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

theorem GlobalTheory.EigenNorm.hermForm_sum_left {κ : Type*} (s : Finset κ) (z : κ → Fin g → ℂ) (w : Fin g → ℂ) :
    hermForm Hm (∑ i ∈ s, z i) w = ∑ i ∈ s, hermForm Hm (z i) w := by sorry
