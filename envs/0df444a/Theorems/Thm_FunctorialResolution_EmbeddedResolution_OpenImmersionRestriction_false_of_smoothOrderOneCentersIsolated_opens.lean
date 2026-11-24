-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_OpenImmersionRestriction_false_of_smoothOrderOneCentersIsolated_opens
-- name    : FunctorialResolution.EmbeddedResolution.OpenImmersionRestriction.false_of_smoothOrderOneCentersIsolated_opens
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T10:46:24.872841+00:00
-- url     : https://prove2.me/theorems/1c08b929-b1ef-44da-8141-a8f436214a0b
-- title:
--   Open Immersion Restriction: false of smooth Order One Centers Isolated opens
-- statement:
--   The Open Immersion Restriction construction uses the false of smooth Order One Centers Isolated opens property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/StrictTransformIsolation/SmoothOrderOneCenters.lean#L125-L180
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/StrictTransformIsolation/SmoothOrderOneCenters.lean#L125-L180

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossings
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IdealSheafOrder
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_AlgebraicPreliminaries_GenericPointImage
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_StrictTransformIsolation_RestrictionToOpens
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_PrincipalizationCertificate
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_StrictTransformIsolation_SmoothOrderOneCenters
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
open FunctorialResolution FunctorialResolution.EmbeddedResolution FunctorialResolution.EmbeddedResolution.OpenImmersionRestriction

theorem FunctorialResolution.EmbeddedResolution.OpenImmersionRestriction.false_of_smoothOrderOneCentersIsolated_opens {V : VanishingAssignment.{u}} (hV : IdealSheafGeometryHypotheses V)
    (hG : SmoothVanishingHypotheses V) {k : Type u} [Field k] [CharZero k] {W : Scheme.{u}}
    (p : W ⟶ Spec (CommRingCat.of k)) (I Z : W.IdealSheafData) (m : ℕ) (Mem : Set ↥W)
    (C : PointedIrreducibleClosed W) (U : W.Opens) (hptU : C.pt ∈ (U : Set ↥W))
    (hIso : SmoothOrderOneCentersIsolated V U.toScheme (U.ι ≫ p) (I.comap U.ι) m
      (U.ι.base ⁻¹' Mem) (Z.comap U.ι))
    (hp : Smooth p) (hm : m = 1)
    (hsm : Smooth ((V W ⟨C.S, C.closedS⟩).subschemeι ≫ p))
    (hcomp : ∀ E ∈ irreducibleComponents ↥W, ¬ E ⊆ C.S)
    (hxi : C.xi ∉ (Z.support : Set ↥W))
    (hdisj : Disjoint C.S Mem)
    (hagree : ∀ x ∈ C.S, AgreeNear I (V W ⟨C.S, C.closedS⟩) x)
    (hpt : C.pt ∈ (Z.support : Set ↥W)) : False := by sorry
