-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_linearIndependent_tensor_D_of_maximalIdeal
-- name    : FunctorialResolution.EmbeddedResolution.linearIndependent_tensor_D_of_maximalIdeal
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T10:47:52.659078+00:00
-- url     : https://prove2.me/theorems/e45240ce-2c76-4076-8990-279e07911e19
-- title:
--   Embedded Resolution: linear Independent tensor D of maximal Ideal
-- statement:
--   The Embedded Resolution construction uses the linear Independent tensor D of maximal Ideal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/EtaleCoordinates/LocalParameters.lean#L184-L192
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/EtaleCoordinates/LocalParameters.lean#L184-L192

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_LocalParameters
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open FunctorialResolution FunctorialResolution.EmbeddedResolution
variable (k A : Type*) [CommRing k] [CommRing A] [Algebra k A] [IsLocalRing A]
  [IsNoetherianRing A] [Algebra.FormallySmooth k A]
  [Module.Free A (KaehlerDifferential k A)] [Module.Finite A (KaehlerDifferential k A)]
  [Algebra k (IsLocalRing.ResidueField A)]
  [IsScalarTower k A (IsLocalRing.ResidueField A)]
  [Algebra.FormallySmooth k (IsLocalRing.ResidueField A)]
omit [IsNoetherianRing A] [Module.Free A (KaehlerDifferential k A)]
  [Module.Finite A (KaehlerDifferential k A)]

theorem FunctorialResolution.EmbeddedResolution.linearIndependent_tensor_D_of_maximalIdeal {ι : Type*}
    (m : ι → (IsLocalRing.maximalIdeal A : Ideal A))
    (hm : LinearIndependent (IsLocalRing.ResidueField A)
      (fun i : ι => (1 : IsLocalRing.ResidueField A) ⊗ₜ[A] (m i))) :
    LinearIndependent (IsLocalRing.ResidueField A)
      (fun i : ι =>
        (1 : IsLocalRing.ResidueField A) ⊗ₜ[A] (KaehlerDifferential.D k A ((m i : A)))) := by sorry
