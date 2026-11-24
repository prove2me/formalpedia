-- Prove2me | Theorems.Thm_FunctorialResolution_Blowup_exists_lift_affineBlowup
-- name    : FunctorialResolution.Blowup.exists_lift_affineBlowup
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T12:56:45.845377+00:00
-- url     : https://prove2.me/theorems/7624f676-f9da-4342-86c8-fca2b2e724ed
-- title:
--   Blowup: exists lift affine Blowup
-- statement:
--   The Blowup construction uses the exists lift affine Blowup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/Foundations/Blowup/AffineBlowupUniversalLift.lean#L228-L258
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/Foundations/Blowup/AffineBlowupUniversalLift.lean#L228-L258

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_AffineBlowup
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_ReesGrading
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_AffineBlowupUniversalLift
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry
noncomputable section
open FunctorialResolution FunctorialResolution.Blowup
universe u v
variable {R : Type u} [CommRing R]

theorem FunctorialResolution.Blowup.exists_lift_affineBlowup (I : Ideal R) {W : Scheme.{u}} [IsAffine W]
    (g : W ⟶ Spec (CommRingCat.of R)) (a : ↥I)
    (hgen : Ideal.map (globalSectionsRingHom g) I = Ideal.span {globalSectionsRingHom g (a : R)})
    (hnzd : globalSectionsRingHom g (a : R) ∈ nonZeroDivisors Γ(W, ⊤)) :
    ∃ h : W ⟶ affineBlowup I,
      h ≫ AffineBlowup.toSpec I = g ∧
        Set.range h.base ⊆ Set.range (affineBlowupChart I a).base := by sorry
