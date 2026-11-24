-- Prove2me | Theorems.Thm_GlobalTheory_ConjBound_re_lt_of_comm
-- name    : GlobalTheory.ConjBound.re_lt_of_comm
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T12:25:52.429368+00:00
-- url     : https://prove2.me/theorems/6dba4743-10d6-456d-b246-98ecd9025812
-- title:
--   Conj Bound: re lt of comm
-- statement:
--   The Conj Bound construction uses the re lt of comm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ImAdjointOfSpan.lean#L60-L94
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ImAdjointOfSpan.lean#L60-L94

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_EqZeroOfSumEmbeddingMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ImAdjointOfSpan
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory GlobalTheory.ConjBound
open GlobalTheory.EigenNorm
variable {g : ℕ}

theorem GlobalTheory.ConjBound.re_lt_of_comm (Hm : Matrix (Fin g) (Fin g) ℂ) (t : Fin g → ℂ) (κ : ℝ)
    (hpos : ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re)
    (hc : ∀ i j, t i * Hm i j = Hm i j * t j) (ht : ∀ i, ‖t i‖ ^ 2 < κ) (y : Fin g → ℂ) (hy : y ≠ 0) :
    (hermForm Hm (t * y) (t * y)).re < κ * (hermForm Hm y y).re := by sorry
