-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_idealSheafData_eq_of_forall_restrictIdeal_eq
-- name    : FunctorialResolution.EmbeddedResolution.idealSheafData_eq_of_forall_restrictIdeal_eq
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T10:48:27.932802+00:00
-- url     : https://prove2.me/theorems/f1581ba4-33a7-4a36-a172-b767e2545201
-- title:
--   Embedded Resolution: ideal Sheaf Data eq of forall restrict Ideal eq
-- statement:
--   The Embedded Resolution construction uses the ideal Sheaf Data eq of forall restrict Ideal eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/EtaleCoordinates/SubschemeMapFlatness.lean#L167-L185
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/EtaleCoordinates/SubschemeMapFlatness.lean#L167-L185

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

theorem FunctorialResolution.EmbeddedResolution.idealSheafData_eq_of_forall_restrictIdeal_eq {X : Scheme.{u}} (I J : X.IdealSheafData)
    (h : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧ restrictIdeal I U = restrictIdeal J U) : I = J := by sorry
