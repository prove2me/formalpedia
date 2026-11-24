-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_generalizing_subschemeMapOfComap
-- name    : FunctorialResolution.EmbeddedResolution.generalizing_subschemeMapOfComap
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T10:47:35.501167+00:00
-- url     : https://prove2.me/theorems/0617fdb0-f936-45d9-ac9e-c82bad6cf524
-- title:
--   Embedded Resolution: generalizing subscheme Map Of Comap
-- statement:
--   The Embedded Resolution construction uses the generalizing subscheme Map Of Comap property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/EtaleCoordinates/SubschemeMapFlatness.lean#L67-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/EtaleCoordinates/SubschemeMapFlatness.lean#L67-L72

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_IdealSheafOpenRestriction
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossings
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_SubschemeMapFlatness
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry TopologicalSpace
noncomputable section
open FunctorialResolution FunctorialResolution.EmbeddedResolution

theorem FunctorialResolution.EmbeddedResolution.generalizing_subschemeMapOfComap {X Y : Scheme.{u}} (g : Y ⟶ X)
    [AlgebraicGeometry.Flat g] (Z : X.IdealSheafData)
    (y : (Z.comap g).subscheme) (x : Z.subscheme)
    (hx : x ⤳ (subschemeMapOfComap g Z).base y) :
    ∃ y' : (Z.comap g).subscheme, y' ⤳ y ∧ (subschemeMapOfComap g Z).base y' = x := by sorry
