-- Prove2me | Theorems.Thm_GlobalTheory_isIso_of_id_mod_eps
-- name    : GlobalTheory.isIso_of_id_mod_eps
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T15:24:53.943324+00:00
-- url     : https://prove2.me/theorems/39f22e50-500f-58c6-9583-b458eb49ecbb
-- title:
--   Global Theory: is Iso of id mod eps
-- statement:
--   The Global Theory construction uses the is Iso of id mod eps property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/IsIsoOfIdModEpsThickening.lean#L174-L241
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/IsIsoOfIdModEpsThickening.lean#L174-L241

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsInvDer
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_KerAppEqMapAppLEOfIsPullback
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_IsIsoOfIdModEpsThickening
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
open GlobalTheory

theorem GlobalTheory.isIso_of_id_mod_eps : ∀ (K : Type) [Field K] (Y Y' Z' : Scheme.{0}) (q : Y ⟶ Sp K) (π : Y' ⟶ Sp (DualNumber K)) (π' : Z' ⟶ Sp (DualNumber K)) (j : Y ⟶ Y') (j' : Y ⟶ Z') (e : Y' ⟶ Z'), IsPullback j q π (spMap (TrivSqZeroExt.fstHom K K K).toRingHom) → IsPullback j' q π' (spMap (TrivSqZeroExt.fstHom K K K).toRingHom) → Flat π → e ≫ π' = π → j ≫ e = j' → IsIso e := by sorry
