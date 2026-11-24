-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_comap_coordIdeal_singleton_of_notMem
-- name    : FunctorialResolution.EmbeddedResolution.comap_coordIdeal_singleton_of_notMem
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T10:46:41.922181+00:00
-- url     : https://prove2.me/theorems/da04fd12-5b18-4ad1-9f6c-7ae264d5f056
-- title:
--   Embedded Resolution: comap coord Ideal singleton of not Mem
-- statement:
--   The Embedded Resolution construction uses the comap coord Ideal singleton of not Mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/StrictTransformCharts/CoordinateSubstitution.lean#L180-L190
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/StrictTransformCharts/CoordinateSubstitution.lean#L180-L190

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossings
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_IdealSheafData
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_StrictTransformCharts_CoordinateSubstitution
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry Opposite
noncomputable section
open FunctorialResolution FunctorialResolution.EmbeddedResolution

theorem FunctorialResolution.EmbeddedResolution.comap_coordIdeal_singleton_of_notMem {X X₁ : Scheme.{u}} {k : Type u} [Field k]
    {p : X ⟶ Spec (CommRingCat.of k)} {p₁ : X₁ ⟶ Spec (CommRingCat.of k)}
    {U : X.Opens} {V : X₁.Opens} {m : ℕ} {S : Finset (Fin m)} {s : Fin m}
    (c : EtaleChart p U m) (c₁ : EtaleChart p₁ V m)
    (g : V.toScheme ⟶ U.toScheme)
    (hg : c₁.map ≫ coordBlowupSubstMap k m S s = g ≫ c.map)
    (j : Fin m) (hj : j ∉ S) :
    (c.coordIdeal {j}).comap g = c₁.coordIdeal {j} := by sorry
