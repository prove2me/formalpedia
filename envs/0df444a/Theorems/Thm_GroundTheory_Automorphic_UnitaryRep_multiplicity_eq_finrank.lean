-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_multiplicity_eq_finrank
-- name    : GroundTheory.Automorphic.UnitaryRep.multiplicity_eq_finrank
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T12:54:21.673281+00:00
-- url     : https://prove2.me/theorems/9c573887-aafb-5f4f-bdee-e53b39099712
-- title:
--   Unitary Rep: multiplicity eq finrank
-- statement:
--   The Unitary Rep construction uses the multiplicity eq finrank property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TraceFormulaMultiplicity.lean#L186-L204
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TraceFormulaMultiplicity.lean#L186-L204

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
include hsum hirr

theorem GroundTheory.Automorphic.UnitaryRep.multiplicity_eq_finrank
    (hfin : ∀ j, {k : J | (π.restrict (V k) (hinv k)).IsEquivalent
      (π.restrict (V j) (hinv j))}.Finite)
    (c : Quotient (restrictSetoid π hinv)) {σ : UnitaryRep G K}
    (hσ : (π.restrict (V c.out) (hinv c.out)).IsEquivalent σ) :
    FiniteDimensional ℂ (σ.intertwiners π) ∧
      multiplicity π hinv c = Module.finrank ℂ (σ.intertwiners π) := by sorry
