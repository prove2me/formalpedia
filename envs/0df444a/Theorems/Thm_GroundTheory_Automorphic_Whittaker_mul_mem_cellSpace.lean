-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Whittaker_mul_mem_cellSpace
-- name    : GroundTheory.Automorphic.Whittaker.mul_mem_cellSpace
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T00:36:52.488621+00:00
-- url     : https://prove2.me/theorems/4526365a-804f-40e5-a5df-a8af4be26995
-- title:
--   Whittaker: mul mem cell Space
-- statement:
--   The Whittaker construction uses the mul mem cell Space property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerDistribution.lean#L349-L402
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerDistribution.lean#L349-L402

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

theorem GroundTheory.Automorphic.Whittaker.mul_mem_cellSpace {g : GL (Fin n) F} {U : Set (GL (Fin n) F)}
    (hUinv : ∀ k : NN F n, ∀ x ∈ U, k • x ∈ U) (hUge : U ⊆ cellGe g)
    {V : Set (Fin n → F)} (hV : IsClopen V) {r : GL (Fin n) F → ℂ}
    (hr : r ∈ relSpan (chi (n := n) ψ₀) U ⊔ (supportedIn U ⊓ vanishingOn (cellLe g))) :
    (fun x => (cellMinor (bruhatCell g) ⁻¹' V).indicator 1 x * r x) ∈
      relSpan (chi (n := n) ψ₀) U ⊔ (supportedIn U ⊓ vanishingOn (cellLe g)) := by sorry
