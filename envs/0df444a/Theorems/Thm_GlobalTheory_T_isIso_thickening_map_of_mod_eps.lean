-- Prove2me | Theorems.Thm_GlobalTheory_T_isIso_thickening_map_of_mod_eps
-- name    : GlobalTheory.T.isIso_thickening_map_of_mod_eps
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T20:51:04.775263+00:00
-- url     : https://prove2.me/theorems/ff3d64ff-d082-473c-aebd-8f295264a0c9
-- title:
--   T: is Iso thickening map of mod eps
-- statement:
--   The T construction uses the is Iso thickening map of mod eps property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/IsIsoThickeningMapOfModEpsStatement.lean#L13-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/IsIsoThickeningMapOfModEpsStatement.lean#L13-L14

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_IsIsoThickeningMapOfModEps
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsSymm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_IsIsoThickeningMapOfModEpsStatement
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
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.isIso_thickening_map_of_mod_eps : ∀ (Y Y' Z' : Scheme.{0}) (q : Y ⟶ Sp ℂ) (π : Y' ⟶ Sp (DualNumber ℂ)) (π' : Z' ⟶ Sp (DualNumber ℂ)) (j : Y ⟶ Y') (j' : Y ⟶ Z') (e : Y' ⟶ Z'), IsPullback j q π (spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom) → IsPullback j' q π' (spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom) → Flat π → e ≫ π' = π → j ≫ e = j' → IsIso e := by sorry
