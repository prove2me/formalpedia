-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_exists_local_parameters
-- name    : FunctorialResolution.EmbeddedResolution.exists_local_parameters
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T10:46:52.113863+00:00
-- url     : https://prove2.me/theorems/572b3343-9c04-4a8c-a9da-0bd18cc0f733
-- title:
--   Embedded Resolution: exists local parameters
-- statement:
--   The Embedded Resolution construction uses the exists local parameters property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/EtaleCoordinates/LocalParameters.lean#L195-L235
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/EtaleCoordinates/LocalParameters.lean#L195-L235

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
omit [Module.Free A (KaehlerDifferential k A)] [Module.Finite A (KaehlerDifferential k A)]

theorem FunctorialResolution.EmbeddedResolution.exists_local_parameters :
    ∃ (h : ℕ) (y : Fin h → A),
      Ideal.span (Set.range y) = IsLocalRing.maximalIdeal A ∧
      LinearIndependent (IsLocalRing.ResidueField A)
        (fun i : Fin h =>
          (1 : IsLocalRing.ResidueField A) ⊗ₜ[A] (KaehlerDifferential.D k A (y i))) := by sorry
