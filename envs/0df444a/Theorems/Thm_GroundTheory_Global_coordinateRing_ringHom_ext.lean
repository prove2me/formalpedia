-- Prove2me | Theorems.Thm_GroundTheory_Global_coordinateRing_ringHom_ext
-- name    : GroundTheory.Global.coordinateRing_ringHom_ext
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T23:40:31.737156+00:00
-- url     : https://prove2.me/theorems/3b9fcfd0-3180-4fcc-9018-1bf6bfbcd228
-- title:
--   Global: coordinate Ring ring Hom ext
-- statement:
--   The Global construction uses the coordinate Ring ring Hom ext property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/ReductionLift.lean#L91-L105
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/ReductionLift.lean#L91-L105

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
omit [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]

theorem GroundTheory.Global.coordinateRing_ringHom_ext {S : Type*} [CommRing S]
    {f g : W.toAffine.CoordinateRing →+* S}
    (h₁ : ∀ c : 𝒪, f (algebraMap 𝒪 _ c) = g (algebraMap 𝒪 _ c))
    (h₂ : f (CoordinateRing.mk W (C X)) = g (CoordinateRing.mk W (C X)))
    (h₃ : f (CoordinateRing.mk W Y) = g (CoordinateRing.mk W Y)) : f = g := by sorry
