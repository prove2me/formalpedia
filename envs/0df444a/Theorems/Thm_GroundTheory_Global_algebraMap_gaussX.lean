-- Prove2me | Theorems.Thm_GroundTheory_Global_algebraMap_gaussX
-- name    : GroundTheory.Global.algebraMap_gaussX
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T23:41:06.29264+00:00
-- url     : https://prove2.me/theorems/9acfaf87-feee-4af2-8896-dd0d801de428
-- title:
--   Global: algebra Map gauss X
-- statement:
--   The Global construction uses the algebra Map gauss X property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/ReductionGauss.lean#L261-L268
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/ReductionGauss.lean#L261-L268

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

theorem GroundTheory.Global.algebraMap_gaussX :
    algebraMap (gaussRing W) (W.baseChange K).toAffine.FunctionField (gaussX W) =
      genX (W.baseChange K) := by sorry
