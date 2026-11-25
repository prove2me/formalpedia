-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_WittOrbit_int_map
-- name    : GlobalTheory.CompanionTheory.WittOrbit.int_map
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T12:01:53.799618+00:00
-- url     : https://prove2.me/theorems/07b533f3-8d37-5947-806b-077fa35554a1
-- title:
--   Witt Orbit: int map
-- statement:
--   The Witt Orbit construction uses the int map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MembershipProofs/CharacterAugmentationSubspaceQuotientActionTop.lean#L18-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MembershipProofs/CharacterAugmentationSubspaceQuotientActionTop.lean#L18-L22

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

theorem GlobalTheory.CompanionTheory.WittOrbit.int_map {m n : Type} {X : Matrix m n E} (hs : ∀ z ∈ A, c z ∈ A) (hX : ∀ i j, X i j ∈ A) :
    ∀ i j, (X.map c) i j ∈ A := by sorry
