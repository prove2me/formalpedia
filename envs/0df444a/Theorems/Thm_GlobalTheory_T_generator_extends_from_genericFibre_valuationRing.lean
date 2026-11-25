-- Prove2me | Theorems.Thm_GlobalTheory_T_generator_extends_from_genericFibre_valuationRing
-- name    : GlobalTheory.T.generator_extends_from_genericFibre_valuationRing
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T15:37:26.523509+00:00
-- url     : https://prove2.me/theorems/4989aa02-5bb8-4502-ac6b-4b5a4805fd9b
-- title:
--   T: generator extends from generic Fibre valuation Ring
-- statement:
--   The T construction uses the generator extends from generic Fibre valuation Ring property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/GeneratorExtendsFromGenericFibreValuationRingStatement.lean#L12-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/GeneratorExtendsFromGenericFibreValuationRingStatement.lean#L12-L13

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_GeneratorExtendsFromGenericFibreValuationRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Clauses
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_AlWellDefSt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_GeneratorExtendsFromGenericFibreValuationRingStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Pdiv GlobalTheory.AbLaw
open scoped CategoryTheory.Obj TensorProduct
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.generator_extends_from_genericFibre_valuationRing : ∀ (O K : Type) [CommRing O] [IsDomain O] [ValuationRing O] [Ring.DimensionLEOne O] [Field K] [IsAlgClosed K] [Algebra O K] [IsFractionRing O K] (X XK : Scheme.{0}) (f : X ⟶ Sp O) (j : XK ⟶ X) (fK : XK ⟶ Sp K), IsPullback j fK f (spMap (algebraMap O K)) → Smooth f → QuasiCompact f → GeometricallyIntegral f → ∀ M : LB X, M.IsLB → Triv (M.pull j) → Triv M := by sorry
