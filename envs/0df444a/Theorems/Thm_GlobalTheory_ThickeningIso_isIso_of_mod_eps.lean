-- Prove2me | Theorems.Thm_GlobalTheory_ThickeningIso_isIso_of_mod_eps
-- name    : GlobalTheory.ThickeningIso.isIso_of_mod_eps
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T21:08:04.06959+00:00
-- url     : https://prove2.me/theorems/7e1a2844-2c82-4543-bf5b-9ceba0654b55
-- title:
--   Thickening Iso: is Iso of mod eps
-- statement:
--   The Thickening Iso construction uses the is Iso of mod eps property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/IsIsoThickeningMapOfModEps.lean#L131-L145
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/IsIsoThickeningMapOfModEps.lean#L131-L145

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsSymm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_IsAffineOfIsAffinePullbackQuotientOfIsNilpotent
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_IsIsoThickeningMapOfModEps
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
open GlobalTheory GlobalTheory.ThickeningIso

theorem GlobalTheory.ThickeningIso.isIso_of_mod_eps : ∀ (Y Y' Z' : Scheme.{0}) (q : Y ⟶ Sp ℂ) (π : Y' ⟶ Sp (DualNumber ℂ)) (π' : Z' ⟶ Sp (DualNumber ℂ)) (j : Y ⟶ Y') (j' : Y ⟶ Z') (e : Y' ⟶ Z'), IsPullback j q π (spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom) → IsPullback j' q π' (spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom) → Flat π → e ≫ π' = π → j ≫ e = j' → IsIso e := by sorry
