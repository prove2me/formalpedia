-- Prove2me | Theorems.Thm_GroundTheory_Global_comp_algebraMap_gaussLift
-- name    : GroundTheory.Global.comp_algebraMap_gaussLift
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:55:24.398281+00:00
-- url     : https://prove2.me/theorems/2b195026-2147-567b-8846-f83d83b150c6
-- title:
--   Global: comp algebra Map gauss Lift
-- statement:
--   The Global construction uses the comp algebra Map gauss Lift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/ReductionLift.lean#L195-L210
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/ReductionLift.lean#L195-L210

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
variable (K : Type*) [Field K] [Algebra 𝒪 K] [IsFractionRing 𝒪 K] (M : Type*) [Field M]
  [Algebra Λ M]

theorem GroundTheory.Global.comp_algebraMap_gaussLift (σ : (W.baseChange K).toAffine.FunctionField →+* M)
    (hσ : ∀ c : 𝒪, σ (algebraMap 𝒪 _ c) = algebraMap Λ M (j c))
    (hX : σ (genX (W.baseChange K)) = algebraMap Λ M x)
    (hY : σ (genY (W.baseChange K)) = algebraMap Λ M y) :
    σ.comp (algebraMap (gaussRing W) _) = (algebraMap Λ M).comp (gaussLift W j hxy hx) := by sorry
