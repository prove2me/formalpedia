-- Prove2me | Theorems.Thm_GlobalTheory_PeriodCoord_exists_finset_of_mem_nhds
-- name    : GlobalTheory.PeriodCoord.exists_finset_of_mem_nhds
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T18:42:46.377116+00:00
-- url     : https://prove2.me/theorems/9e11a813-3221-49dc-94b5-751f75818136
-- title:
--   Period Coord: exists finset of mem nhds
-- statement:
--   The Period Coord construction uses the exists finset of mem nhds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsFinsetOfMemNhds.lean#L119-L128
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsFinsetOfMemNhds.lean#L119-L128

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_DifferentiableOnLeftInverse
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_IsPreconnectedBlockUnits
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsFinsetOfMemNhds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix
open scoped ComplexConjugate
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.PeriodCoord
noncomputable section
variable {g : ℕ}

theorem GlobalTheory.PeriodCoord.exists_finset_of_mem_nhds {L : Type} {f₀ : L → Fin g → ℂ} {U : Set (L → Fin g → ℂ)} (hU : U ∈ nhds f₀) :
    ∃ (s : Finset L) (ε : ℝ), 0 < ε ∧ ∀ f, (∀ x ∈ s, ‖f x - f₀ x‖ < ε) → f ∈ U := by sorry
