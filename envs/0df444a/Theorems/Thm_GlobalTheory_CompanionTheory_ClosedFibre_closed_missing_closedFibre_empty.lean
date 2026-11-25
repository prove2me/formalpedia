-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_ClosedFibre_closed_missing_closedFibre_empty
-- name    : GlobalTheory.CompanionTheory.ClosedFibre.closed_missing_closedFibre_empty
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T12:01:11.405908+00:00
-- url     : https://prove2.me/theorems/d1d52706-2c09-4068-a389-e6aad4e749ea
-- title:
--   Closed Fibre: closed missing closed Fibre empty
-- statement:
--   The Closed Fibre construction uses the closed missing closed Fibre empty property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ClosedMissingClosedFibreEmpty.lean#L7-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ClosedMissingClosedFibreEmpty.lean#L7-L23

import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_FormalAlgebraisation_GEClosedProj
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__FormalAlgebraisation_7c2ebf494af3a4ae
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ClosedMissingClosedFibreEmpty
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Out PositivityTheory.FormalThickening
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.ClosedFibre

theorem GlobalTheory.CompanionTheory.ClosedFibre.closed_missing_closedFibre_empty : ∀ (R : Type) [CommRing R] (I : Ideal R), IsAdicComplete I R →
  ∀ (X : Over (Spec (CommRingCat.of R))), UniversallyClosed X.hom →
  ∀ Z : Set X.left, IsClosed Z → (∀ x ∈ Z, ¬ (I ≤ (X.hom.base x).asIdeal)) → Z = ∅ := by sorry
