-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Whittaker_supportedIn_le_of_irrelevant
-- name    : GroundTheory.Automorphic.Whittaker.supportedIn_le_of_irrelevant
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T00:36:26.838442+00:00
-- url     : https://prove2.me/theorems/b3031059-102f-4e08-8803-e8208e7dd298
-- title:
--   Whittaker: supported In le of irrelevant
-- statement:
--   The Whittaker construction uses the supported In le of irrelevant property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerDistribution.lean#L246-L296
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerDistribution.lean#L246-L296

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

theorem GroundTheory.Automorphic.Whittaker.supportedIn_le_of_irrelevant (hψ : Continuous ψ₀) {U C : Set (GL (Fin n) F)}
    (hU : IsOpen U) (hC : IsClosed C) (hUinv : ∀ k : NN F n, ∀ x ∈ U, k • x ∈ U)
    {w : Equiv.Perm (Fin n)} {t : Fin n → Fˣ}
    (hO : U ∩ C = orbit (NN F n) (Iwasawa.diagGL F n t * permGL F w))
    (hirr : Irrelevant ψ₀ w t) :
    supportedIn U ≤ relSpan (chi (n := n) ψ₀) U ⊔ (supportedIn U ⊓ vanishingOn C) := by sorry
