-- Prove2me | Theorems.Thm_FunctorialResolution_Blowup_globalSectionsRingHom_eq
-- name    : FunctorialResolution.Blowup.globalSectionsRingHom_eq
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T12:55:36.157602+00:00
-- url     : https://prove2.me/theorems/f9bdfcaa-fb80-490e-8931-78f5ccec99df
-- title:
--   Blowup: global Sections Ring Hom eq
-- statement:
--   The Blowup construction uses the global Sections Ring Hom eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/Foundations/Blowup/AffineBlowupUniversalLift.lean#L167-L168
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/Foundations/Blowup/AffineBlowupUniversalLift.lean#L167-L168

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

theorem FunctorialResolution.Blowup.globalSectionsRingHom_eq {W : Scheme.{u}} (g : W ⟶ Spec (CommRingCat.of R)) :
    globalSectionsRingHom g = ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ g.appTop).hom := by sorry
