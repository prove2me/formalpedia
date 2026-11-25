-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Whittaker_cell_relevant
-- name    : GroundTheory.Automorphic.Whittaker.cell_relevant
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T00:41:07.631132+00:00
-- url     : https://prove2.me/theorems/69cc103e-5ca0-4406-8df3-fb757d41e9e4
-- title:
--   Whittaker: cell relevant
-- statement:
--   The Whittaker construction uses the cell relevant property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerDistribution.lean#L438-L571
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerDistribution.lean#L438-L571

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerLSpace
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerOrbit
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerGroups
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerCells
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerRelevance
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerDistribution
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Whittaker
open Set Topology MulAction Matrix DoubleCoset ValuativeRel
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] {n : ℕ}
attribute [local instance] biAction
variable [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
attribute [local instance] totallyDisconnectedSpace_localField
attribute [local instance] continuousSMul_biAction
variable (ψ₀ : AddChar F ℂ)

theorem GroundTheory.Automorphic.Whittaker.cell_relevant (hψ : Continuous ψ₀) (hψ₁ : ψ₀ ≠ 1) {g : GL (Fin n) F}
    {U : Set (GL (Fin n) F)} (hU : IsOpen U) (hUinv : ∀ k : NN F n, ∀ x ∈ U, k • x ∈ U)
    (hUge : U ⊆ cellGe g) (hcellU : ∀ h, bruhatCell h = bruhatCell g → h ∈ U)
    (hUσ : ∀ x, sigma x ∈ U ↔ x ∈ U)
    (hσcell : ∀ h : GL (Fin n) F, bruhatCell h = bruhatCell g → bruhatCell (sigma h) = bruhatCell g)
    {f : GL (Fin n) F → ℂ} (hf : f ∈ supportedIn U) :
    f - sigmaL f ∈ relSpan (chi (n := n) ψ₀) U ⊔ (supportedIn U ⊓ vanishingOn (cellLe g)) := by sorry
