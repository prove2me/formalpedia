-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_ringKrullDim_stalk_le_of_etale_affineSpace
-- name    : FunctorialResolution.EmbeddedResolution.ringKrullDim_stalk_le_of_etale_affineSpace
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T10:49:08.805039+00:00
-- url     : https://prove2.me/theorems/edb7a379-1aa6-4b7d-ade0-ad2a91d850bd
-- title:
--   Embedded Resolution: ring Krull Dim stalk le of etale affine Space
-- statement:
--   The Embedded Resolution construction uses the ring Krull Dim stalk le of etale affine Space property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/EtaleCoordinates/StalkKrullDimension.lean#L190-L203
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/EtaleCoordinates/StalkKrullDimension.lean#L190-L203

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_SmoothRegular
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_AlgebraicPreliminaries_AffineSpaceJacobson
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StalkKrullDimension
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
open FunctorialResolution FunctorialResolution.EmbeddedResolution

theorem FunctorialResolution.EmbeddedResolution.ringKrullDim_stalk_le_of_etale_affineSpace {k : Type u} [Field k] {m : ℕ} {Y : Scheme.{u}}
    (c : Y ⟶ AffineSpace (ULift.{u} (Fin m)) (Spec (CommRingCat.of k)))
    [AlgebraicGeometry.Etale c] (y : Y) [IsNoetherianRing (Y.presheaf.stalk y)] :
    ringKrullDim (Y.presheaf.stalk y) ≤ ((m : ℕ∞) : WithBot ℕ∞) := by sorry
