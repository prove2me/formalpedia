-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_exists_local_parameters_and_dual_derivations
-- name    : FunctorialResolution.EmbeddedResolution.exists_local_parameters_and_dual_derivations
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T10:46:54.455784+00:00
-- url     : https://prove2.me/theorems/57708617-2386-4abb-9031-6d2e2b858c2c
-- title:
--   Embedded Resolution: exists local parameters and dual derivations
-- statement:
--   The Embedded Resolution construction uses the exists local parameters and dual derivations property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/EtaleCoordinates/LocalParameters.lean#L237-L327
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/EtaleCoordinates/LocalParameters.lean#L237-L327

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

theorem FunctorialResolution.EmbeddedResolution.exists_local_parameters_and_dual_derivations :
    ∃ (h : ℕ) (y : Fin h → A) (δ : Fin h → Derivation k A A),
      Ideal.span (Set.range y) = IsLocalRing.maximalIdeal A ∧
      ∀ i j : Fin h, δ i (y j) = if i = j then 1 else 0 := by sorry
