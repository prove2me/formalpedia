-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_local_derivation_lift_smooth_over_field
-- name    : GlobalTheory.T.exists_local_derivation_lift_smooth_over_field
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T20:37:08.2338+00:00
-- url     : https://prove2.me/theorems/b1bae068-8db1-4016-842a-542719109cba
-- title:
--   T: exists local derivation lift smooth over field
-- statement:
--   The T construction uses the exists local derivation lift smooth over field property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsLocalDerivationLiftSmoothOverFieldStatement.lean#L13-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsLocalDerivationLiftSmoothOverFieldStatement.lean#L13-L14

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsLocalDerivationLiftSmoothOverField
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsInvDer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsLocalDerivationLiftSmoothOverFieldStatement
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

theorem GlobalTheory.T.exists_local_derivation_lift_smooth_over_field : ∀ (K : Type) [Field K] (R : Type) [CommRing R] (x₀ : R →+* K) (Y X : Scheme.{0}) (q : Y ⟶ Sp K) (p : X ⟶ Sp R) (m : Y ⟶ X) (D : R → K) (W₀ : X.Opens), Smooth p → m ≫ p = q ≫ spMap x₀ → IsDerK x₀ D → IsAffineOpen W₀ → ∃ d, LocDerK q p m D W₀ d := by sorry
