-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_finrank_intertwiners_eq_card
-- name    : GroundTheory.Automorphic.UnitaryRep.finrank_intertwiners_eq_card
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T01:05:28.525337+00:00
-- url     : https://prove2.me/theorems/acc6ae7c-8b49-43f0-9977-2575450fe712
-- title:
--   Unitary Rep: finrank intertwiners eq card
-- statement:
--   The Unitary Rep construction uses the finrank intertwiners eq card property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TraceFormulaMultiplicity.lean#L116-L180
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TraceFormulaMultiplicity.lean#L116-L180

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_TraceFormulaSpectral
import Definitions.Def_GroundTheory_AutomorphicForms_UnitaryRepresentations_ExistsEqAlgebraMapOfIsSelfAdjoint
import Definitions.Def_GroundTheory_AutomorphicForms_TraceFormulaMultiplicity
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ContinuousLinearMap
open scoped InnerProductSpace
open GroundTheory GroundTheory.Automorphic
noncomputable section
open GroundTheory.Automorphic.UnitaryRep
variable {G : Type*} [Group G] [TopologicalSpace G]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
variable {π : UnitaryRep G H} {J : Type*} {V : J → Submodule ℂ H} [∀ j, CompleteSpace (V j)]
  (hinv : ∀ j, π.IsInvariant (V j))
variable (hsum : IsHilbertSum ℂ (fun j => V j) fun j => (V j).subtypeₗᵢ)
variable (hirr : ∀ j, (π.restrict (V j) (hinv j)).IsIrreducible)
variable {σ : UnitaryRep G K}
include hsum hirr

theorem GroundTheory.Automorphic.UnitaryRep.finrank_intertwiners_eq_card (hσ : σ.IsIrreducible)
    (hW : {j | (π.restrict (V j) (hinv j)).IsEquivalent σ}.Finite) :
    FiniteDimensional ℂ (σ.intertwiners π) ∧
      Module.finrank ℂ (σ.intertwiners π) = Nat.card (EquivSummands hinv σ) := by sorry
