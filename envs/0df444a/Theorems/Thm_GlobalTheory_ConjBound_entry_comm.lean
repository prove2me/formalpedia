-- Prove2me | Theorems.Thm_GlobalTheory_ConjBound_entry_comm
-- name    : GlobalTheory.ConjBound.entry_comm
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T12:26:06.538584+00:00
-- url     : https://prove2.me/theorems/40d3d1ae-3950-4a44-badb-2833f6c91f53
-- title:
--   Conj Bound: entry comm
-- statement:
--   The Conj Bound construction uses the entry comm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ImAdjointOfSpan.lean#L44-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ImAdjointOfSpan.lean#L44-L58

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

theorem GlobalTheory.ConjBound.entry_comm (Hm : Matrix (Fin g) (Fin g) ℂ) (t : Fin g → ℂ)
    (h : ∀ z w, (hermForm Hm (t * z) w).im = (hermForm Hm z (star t * w)).im) (i j : Fin g) :
    t i * Hm i j = Hm i j * t j := by sorry
