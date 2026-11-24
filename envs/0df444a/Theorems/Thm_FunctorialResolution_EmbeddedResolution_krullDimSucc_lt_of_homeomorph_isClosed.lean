-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_krullDimSucc_lt_of_homeomorph_isClosed
-- name    : FunctorialResolution.EmbeddedResolution.krullDimSucc_lt_of_homeomorph_isClosed
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T12:48:17.099086+00:00
-- url     : https://prove2.me/theorems/3027d630-8288-4762-aab4-886112d8d42a
-- title:
--   Embedded Resolution: krull Dim Succ lt of homeomorph is Closed
-- statement:
--   The Embedded Resolution construction uses the krull Dim Succ lt of homeomorph is Closed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/IdealPrincipalization/KrullDimClosedSubset.lean#L188-L198
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/IdealPrincipalization/KrullDimClosedSubset.lean#L188-L198

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_MarkedBlowupSequence_MarkedSequenceOfBlowups
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_KrullDimClosedSubset
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u v
open TopologicalSpace AlgebraicGeometry
open FunctorialResolution FunctorialResolution.EmbeddedResolution

theorem FunctorialResolution.EmbeddedResolution.krullDimSucc_lt_of_homeomorph_isClosed (X Z : Scheme.{u}) (Y : Set ↥X)
    (hY : IsClosed Y) (hne : Y.Nonempty)
    (hcomp : ∀ C ∈ irreducibleComponents ↥X, ¬ C ⊆ Y)
    (hfin : topologicalKrullDim ↥X < ⊤)
    (e : ↥Z ≃ₜ ↥Y) :
    krullDimSucc Z < krullDimSucc X := by sorry
