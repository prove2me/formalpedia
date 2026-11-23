-- Prove2me | Theorems.Thm_GroundTheory_Global_algebraMap_gaussRing_functionField
-- name    : GroundTheory.Global.algebraMap_gaussRing_functionField
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:40:02.559569+00:00
-- url     : https://prove2.me/theorems/a8dc3e67-734c-4db4-86b9-d2da1a3ccf17
-- title:
--   Global: algebra Map gauss Ring function Field
-- statement:
--   The Global construction uses the algebra Map gauss Ring function Field property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/ReductionGauss.lean#L255-L259
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/ReductionGauss.lean#L255-L259

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_FunctionFieldPoint
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_ReductionGauss
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Global
noncomputable section
open IsLocalRing Polynomial WeierstrassCurve.Affine GroundTheory.Arith.Abelian
open scoped Polynomial.Bivariate
variable {𝒪 : Type*} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
  (W : WeierstrassCurve 𝒪)
variable (K : Type*) [Field K] [Algebra 𝒪 K] [IsFractionRing 𝒪 K]

theorem GroundTheory.Global.algebraMap_gaussRing_functionField (a : W.toAffine.CoordinateRing) :
    algebraMap (gaussRing W) (W.baseChange K).toAffine.FunctionField
      (algebraMap W.toAffine.CoordinateRing _ a) =
        algebraMap (W.baseChange K).toAffine.CoordinateRing _ (coordBase W K a) := by sorry
