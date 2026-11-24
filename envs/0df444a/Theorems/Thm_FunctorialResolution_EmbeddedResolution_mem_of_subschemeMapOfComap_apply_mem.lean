-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_mem_of_subschemeMapOfComap_apply_mem
-- name    : FunctorialResolution.EmbeddedResolution.mem_of_subschemeMapOfComap_apply_mem
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T10:47:45.681155+00:00
-- url     : https://prove2.me/theorems/9fe9a848-adbc-43ef-b8c2-b6bff7705457
-- title:
--   Embedded Resolution: mem of subscheme Map Of Comap apply mem
-- statement:
--   The Embedded Resolution construction uses the mem of subscheme Map Of Comap apply mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/EtaleCoordinates/SubschemeMapFlatness.lean#L187-L212
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/EtaleCoordinates/SubschemeMapFlatness.lean#L187-L212

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

theorem FunctorialResolution.EmbeddedResolution.mem_of_subschemeMapOfComap_apply_mem {X Y : Scheme.{u}} (g : Y ⟶ X) (Z : X.IdealSheafData)
    (A : Set X) (W : Z.subscheme.Opens) (W' : (Z.comap g).subscheme.Opens)
    (hW : (W : Set Z.subscheme) = {w | connectedComponent w ⊆ ⇑Z.subschemeι.base ⁻¹' A})
    (hW' : (W' : Set (Z.comap g).subscheme) =
      {w | connectedComponent w ⊆ ⇑(Z.comap g).subschemeι.base ⁻¹' (⇑g.base ⁻¹' A)})
    (y : (Z.comap g).subscheme) (hy : (subschemeMapOfComap g Z).base y ∈ W) : y ∈ W' := by sorry
