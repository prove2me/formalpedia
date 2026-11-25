-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_restrictIdeal_eq_top_iff_forall_notMem_support
-- name    : FunctorialResolution.EmbeddedResolution.restrictIdeal_eq_top_iff_forall_notMem_support
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T11:55:44.951277+00:00
-- url     : https://prove2.me/theorems/c3107d20-ac2e-45af-a564-3ed18fafacf1
-- title:
--   Embedded Resolution: restrict Ideal eq top iff forall not Mem support
-- statement:
--   The Embedded Resolution construction uses the restrict Ideal eq top iff forall not Mem support property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/EtaleCoordinates/StrictNormalCrossings.lean#L19-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/EtaleCoordinates/StrictNormalCrossings.lean#L19-L46

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossings
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

theorem FunctorialResolution.EmbeddedResolution.restrictIdeal_eq_top_iff_forall_notMem_support {X : Scheme.{u}} (I : X.IdealSheafData)
    (U : X.Opens) :
    restrictIdeal I U = ⊤ ↔ ∀ x : X, x ∈ U → x ∉ I.support := by sorry
