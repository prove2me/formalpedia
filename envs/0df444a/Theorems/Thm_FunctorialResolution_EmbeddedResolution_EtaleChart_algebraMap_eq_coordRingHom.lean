-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleChart_algebraMap_eq_coordRingHom
-- name    : FunctorialResolution.EmbeddedResolution.EtaleChart.algebraMap_eq_coordRingHom
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T13:16:04.25027+00:00
-- url     : https://prove2.me/theorems/4a4a6cce-5df2-4bb4-aec2-bf5792ae9728
-- title:
--   Etale Chart: algebra Map eq coord Ring Hom
-- statement:
--   The Etale Chart construction uses the algebra Map eq coord Ring Hom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/EtaleCoordinates/ChartRing.lean#L152-L154
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/EtaleCoordinates/ChartRing.lean#L152-L154

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_EtaleCoordinates
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossings
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdealSheaf
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_IdealSheafData
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_SchemeMorphismProperties
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_ChartRing
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace
noncomputable section
open FunctorialResolution FunctorialResolution.EmbeddedResolution
variable {X : Scheme.{u}} {k : Type u} [Field k] {p : X ⟶ Spec (CommRingCat.of k)}
  {U : X.Opens} {m : ℕ}

theorem FunctorialResolution.EmbeddedResolution.EtaleChart.algebraMap_eq_coordRingHom (c : EtaleChart p U m) :
    @algebraMap (MvPolynomial (ULift.{u} (Fin m)) k) Γ(X, U) _ _ c.algebra = c.coordRingHom := by sorry
