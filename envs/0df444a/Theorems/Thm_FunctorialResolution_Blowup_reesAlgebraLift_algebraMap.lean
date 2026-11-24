-- Prove2me | Theorems.Thm_FunctorialResolution_Blowup_reesAlgebraLift_algebraMap
-- name    : FunctorialResolution.Blowup.reesAlgebraLift_algebraMap
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T12:55:45.422236+00:00
-- url     : https://prove2.me/theorems/40b0390e-e3e2-4fba-a2ea-434d225840f1
-- title:
--   Blowup: rees Algebra Lift algebra Map
-- statement:
--   The Blowup construction uses the rees Algebra Lift algebra Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/Foundations/Blowup/AffineBlowupUniversalLift.lean#L135-L145
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/Foundations/Blowup/AffineBlowupUniversalLift.lean#L135-L145

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
variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

theorem FunctorialResolution.Blowup.reesAlgebraLift_algebraMap (I : Ideal R) (φ : R →+* S) (s : S)
    (hI : Ideal.map φ I = Ideal.span {s}) (hs : s ∈ nonZeroDivisors S) (r : R) :
    reesAlgebraLift I φ s hI hs (algebraMap R ↥(reesAlgebra I) r) = φ r := by sorry
