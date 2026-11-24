-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_krullDimSucc_lt_of_topologicalKrullDim_lt
-- name    : FunctorialResolution.EmbeddedResolution.krullDimSucc_lt_of_topologicalKrullDim_lt
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T12:47:58.186496+00:00
-- url     : https://prove2.me/theorems/5c2fca8f-6cd3-4be2-87cd-98897fcc91e2
-- title:
--   Embedded Resolution: krull Dim Succ lt of topological Krull Dim lt
-- statement:
--   The Embedded Resolution construction uses the krull Dim Succ lt of topological Krull Dim lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/IdealPrincipalization/KrullDimClosedSubset.lean#L183-L186
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/IdealPrincipalization/KrullDimClosedSubset.lean#L183-L186

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

theorem FunctorialResolution.EmbeddedResolution.krullDimSucc_lt_of_topologicalKrullDim_lt (Z X : Scheme.{u})
    (h : topologicalKrullDim ↥Z < topologicalKrullDim ↥X)
    (hfin : topologicalKrullDim ↥X < ⊤) :
    krullDimSucc Z < krullDimSucc X := by sorry
