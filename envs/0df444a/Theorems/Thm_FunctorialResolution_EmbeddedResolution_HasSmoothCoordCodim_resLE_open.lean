-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_HasSmoothCoordCodim_resLE_open
-- name    : FunctorialResolution.EmbeddedResolution.HasSmoothCoordCodim.resLE_open
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T11:53:12.850519+00:00
-- url     : https://prove2.me/theorems/cf5f72d7-b0d0-5796-a8d1-6764b54d4911
-- title:
--   Has Smooth Coord Codim: res LE open
-- statement:
--   The Has Smooth Coord Codim construction uses the res LE open property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/EtaleCoordinates/SmoothCoordinateCodimensionPullback.lean#L43-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/EtaleCoordinates/SmoothCoordinateCodimensionPullback.lean#L43-L69

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupBasic
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_SmoothCoordinateCodimension
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossings
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_SmoothCoordinateCodimensionPullback
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry
noncomputable section
open FunctorialResolution FunctorialResolution.EmbeddedResolution
open FunctorialResolution.EmbeddedResolution.HasSmoothCoordCodim
variable {k : Type u} [Field k]

theorem FunctorialResolution.EmbeddedResolution.HasSmoothCoordCodim.resLE_open {X X' : Scheme.{u}}
    {s : X' ⟶ Spec (CommRingCat.of k)} {τ : X ⟶ X'} [IsClosedImmersion τ] {c : ℕ}
    (h : HasSmoothCoordCodim s τ c) (O : X'.Opens) :
    HasSmoothCoordCodim (O.ι ≫ s) (τ.resLE O (τ ⁻¹ᵁ O) le_rfl) c := by sorry
