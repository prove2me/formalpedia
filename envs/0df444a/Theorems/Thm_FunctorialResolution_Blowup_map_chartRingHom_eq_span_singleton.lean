-- Prove2me | Theorems.Thm_FunctorialResolution_Blowup_map_chartRingHom_eq_span_singleton
-- name    : FunctorialResolution.Blowup.map_chartRingHom_eq_span_singleton
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T12:40:03.498925+00:00
-- url     : https://prove2.me/theorems/3bd6af75-6f26-4685-9f5d-227ce6d06d45
-- title:
--   Blowup: map chart Ring Hom eq span singleton
-- statement:
--   The Blowup construction uses the map chart Ring Hom eq span singleton property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/Foundations/Blowup/AffineBlowup.lean#L191-L199
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/Foundations/Blowup/AffineBlowup.lean#L191-L199

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_ReesGrading
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_AffineBlowup
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry
open FunctorialResolution FunctorialResolution.Blowup
universe u
variable {R : Type u} [CommRing R]

theorem FunctorialResolution.Blowup.map_chartRingHom_eq_span_singleton (I : Ideal R) (a : ↥I) :
    Ideal.map (chartRingHom I a) I = Ideal.span {chartRingHom I a (a : R)} := by sorry
