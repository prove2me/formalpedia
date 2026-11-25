-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_WittOrbit_map_map_eq
-- name    : GlobalTheory.CompanionTheory.WittOrbit.map_map_eq
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T12:01:47.446937+00:00
-- url     : https://prove2.me/theorems/550c3a2b-b88c-5749-9d8e-5afaaed665c2
-- title:
--   Witt Orbit: map map eq
-- statement:
--   The Witt Orbit construction uses the map map eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MembershipProofs/CharacterAugmentationSubspaceQuotientActionTop.lean#L24-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MembershipProofs/CharacterAugmentationSubspaceQuotientActionTop.lean#L24-L25

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_MembershipCriteria_OrderOKOneInert
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_CharacterAugmentationSubspaceQuotientActionTop
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.CompanionTheory.VacLoc GlobalTheory.CompanionTheory.FinHeis GlobalTheory.WeilM MeasureTheory Matrix ValuativeRel NumberField IsDedekindDomain
open scoped TensorProduct
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.WittOrbit
variable {R : Type} [CommRing R] {E : Type} [CommRing E] [Algebra R E] {c : E →ₐ[R] E} {A : Subring E}

theorem GlobalTheory.CompanionTheory.WittOrbit.map_map_eq {m n : Type} (hc : ∀ z, c (c z) = z) (X : Matrix m n E) : (X.map c).map c = X := by sorry
