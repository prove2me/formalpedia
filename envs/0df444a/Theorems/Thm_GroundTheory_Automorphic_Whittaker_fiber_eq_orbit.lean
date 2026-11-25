-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Whittaker_fiber_eq_orbit
-- name    : GroundTheory.Automorphic.Whittaker.fiber_eq_orbit
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T00:37:06.094994+00:00
-- url     : https://prove2.me/theorems/dd6f7b45-1842-4b15-8f66-3c0f56a2746e
-- title:
--   Whittaker: fiber eq orbit
-- statement:
--   The Whittaker construction uses the fiber eq orbit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerDistribution.lean#L205-L230
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerDistribution.lean#L205-L230

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

theorem GroundTheory.Automorphic.Whittaker.fiber_eq_orbit {g : GL (Fin n) F} {U : Set (GL (Fin n) F)} (hUge : U ⊆ cellGe g)
    (hcellU : ∀ h, bruhatCell h = bruhatCell g → h ∈ U) {x : GL (Fin n) F} (hxU : x ∈ U)
    (hxC : x ∈ cellLe g) :
    ∃ t : Fin n → Fˣ, U ∩ (cellLe g ∩ cellMinor (bruhatCell g) ⁻¹' {cellMinor (bruhatCell g) x}) =
      orbit (NN F n) (Iwasawa.diagGL F n t * permGL F (bruhatCell g)) := by sorry
