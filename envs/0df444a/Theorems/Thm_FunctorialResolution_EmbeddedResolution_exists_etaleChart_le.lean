-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_exists_etaleChart_le
-- name    : FunctorialResolution.EmbeddedResolution.exists_etaleChart_le
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T11:53:21.025799+00:00
-- url     : https://prove2.me/theorems/0888f547-f22f-4269-9cc2-aae4917aa933
-- title:
--   Embedded Resolution: exists etale Chart le
-- statement:
--   The Embedded Resolution construction uses the exists etale Chart le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/EtaleCoordinates/EtaleChartExistence.lean#L361-L369
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/EtaleCoordinates/EtaleChartExistence.lean#L361-L369

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossings
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_AffineOpens
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_EtaleChartExistence
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry TopologicalSpace
noncomputable section
open FunctorialResolution FunctorialResolution.EmbeddedResolution

theorem FunctorialResolution.EmbeddedResolution.exists_etaleChart_le {X : Scheme.{u}} {k : Type u} [Field k]
    (p : X ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.Smooth p] (x : X)
    (W : X.Opens) (hx : x ∈ W) :
    ∃ (U : X.Opens) (m : ℕ), x ∈ U ∧ U ≤ W ∧ IsAffineOpen U ∧ Nonempty (EtaleChart p U m) := by sorry
