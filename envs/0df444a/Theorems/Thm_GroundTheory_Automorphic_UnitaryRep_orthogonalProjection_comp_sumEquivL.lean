-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_orthogonalProjection_comp_sumEquivL
-- name    : GroundTheory.Automorphic.UnitaryRep.orthogonalProjection_comp_sumEquivL
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T01:04:13.538405+00:00
-- url     : https://prove2.me/theorems/f96e67bc-956b-4816-9b88-bc26bce3a4ea
-- title:
--   Unitary Rep: orthogonal Projection comp sum Equiv L
-- statement:
--   The Unitary Rep construction uses the orthogonal Projection comp sum Equiv L property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TraceFormulaMultiplicity.lean#L96-L112
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TraceFormulaMultiplicity.lean#L96-L112

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
open Classical
include hsum

theorem GroundTheory.Automorphic.UnitaryRep.orthogonalProjection_comp_sumEquivL [Fintype (EquivSummands hinv σ)]
    (c : EquivSummands hinv σ → ℂ) (j : J) (k : K) :
    (V j).orthogonalProjectionOnto (sumEquivL hinv c k) =
      if h : (π.restrict (V j) (hinv j)).IsEquivalent σ then
        c ⟨j, h⟩ • summandEquivL hinv ⟨j, h⟩ k else 0 := by sorry
