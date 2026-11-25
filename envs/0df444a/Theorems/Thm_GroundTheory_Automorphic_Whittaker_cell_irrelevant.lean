-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Whittaker_cell_irrelevant
-- name    : GroundTheory.Automorphic.Whittaker.cell_irrelevant
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T00:42:29.083845+00:00
-- url     : https://prove2.me/theorems/09bf62f1-a95a-416f-bf20-2b09ed32274c
-- title:
--   Whittaker: cell irrelevant
-- statement:
--   The Whittaker construction uses the cell irrelevant property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerDistribution.lean#L404-L424
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerDistribution.lean#L404-L424

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

theorem GroundTheory.Automorphic.Whittaker.cell_irrelevant (hψ : Continuous ψ₀) {g : GL (Fin n) F} {U : Set (GL (Fin n) F)}
    (hU : IsOpen U) (hUinv : ∀ k : NN F n, ∀ x ∈ U, k • x ∈ U) (hUge : U ⊆ cellGe g)
    (hcellU : ∀ h, bruhatCell h = bruhatCell g → h ∈ U)
    (hirr : ∀ t, Irrelevant ψ₀ (bruhatCell g) t) :
    supportedIn U ≤ relSpan (chi (n := n) ψ₀) U ⊔ (supportedIn U ⊓ vanishingOn (cellLe g)) := by sorry
