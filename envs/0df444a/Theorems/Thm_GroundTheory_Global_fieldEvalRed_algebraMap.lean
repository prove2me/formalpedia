-- Prove2me | Theorems.Thm_GroundTheory_Global_fieldEvalRed_algebraMap
-- name    : GroundTheory.Global.fieldEvalRed_algebraMap
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T12:56:01.874048+00:00
-- url     : https://prove2.me/theorems/2e14eae3-f9b1-5e7a-a356-5172dccd5f6e
-- title:
--   Global: field Eval Red algebra Map
-- statement:
--   The Global construction uses the field Eval Red algebra Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/ReductionLift.lean#L183-L188
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/ReductionLift.lean#L183-L188

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_ReductionGauss
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_ReductionLift
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
variable {𝒪 : Type*} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] (W : WeierstrassCurve 𝒪)
  {Λ : Type*} [CommRing Λ] [IsDomain Λ] [IsDiscreteValuationRing Λ] (j : 𝒪 →+* Λ) [IsLocalHom j]
  {x y : Λ} (hxy : (W.map j).toAffine.Equation x y)
variable (hx : Function.Injective (eval₂RingHom (ResidueField.map j) (residue Λ x)))

theorem GroundTheory.Global.fieldEvalRed_algebraMap (c : ResidueField 𝒪) :
    fieldEvalRed W j hxy hx (algebraMap (ResidueField 𝒪) _ c) = ResidueField.map j c := by sorry
