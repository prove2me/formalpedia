-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_isStrongResolutionRule_iff
-- name    : FunctorialResolution.EmbeddedResolution.isStrongResolutionRule_iff
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T11:57:47.356802+00:00
-- url     : https://prove2.me/theorems/186c3fdf-bdc3-4a7a-aa03-e91d5642e551
-- title:
--   Embedded Resolution: is Strong Resolution Rule iff
-- statement:
--   The Embedded Resolution construction uses the is Strong Resolution Rule iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/StrongResolution/StrongResolution.lean#L23-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/StrongResolution/StrongResolution.lean#L23-L29

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_StrongResolution_StrongResolution
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

theorem FunctorialResolution.EmbeddedResolution.isStrongResolutionRule_iff (R : ResolutionRule.{u}) :
    IsStrongResolutionRule R ↔
      ∀ (k : Type u) [Field k] [CharZero k] (X : Scheme.{u})
        (f : X ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.LocallyOfFiniteType f]
        [AlgebraicGeometry.QuasiCompact f] [AlgebraicGeometry.IsReduced X],
        IsStrongResolution k X f (R k X f) := by sorry
