-- Prove2me | Theorems.Thm_GroundTheory_Global_algebraMap_gaussY
-- name    : GroundTheory.Global.algebraMap_gaussY
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T23:42:13.816997+00:00
-- url     : https://prove2.me/theorems/bb3b08c0-1d39-4fbb-80b1-9ac1d50166d3
-- title:
--   Global: algebra Map gauss Y
-- statement:
--   The Global construction uses the algebra Map gauss Y property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/ReductionGauss.lean#L270-L277
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/ReductionGauss.lean#L270-L277

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

theorem GroundTheory.Global.algebraMap_gaussY :
    algebraMap (gaussRing W) (W.baseChange K).toAffine.FunctionField (gaussY W) =
      genY (W.baseChange K) := by sorry
