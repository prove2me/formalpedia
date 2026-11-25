-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Whittaker_chi_apply
-- name    : GroundTheory.Automorphic.Whittaker.chi_apply
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T00:35:40.805025+00:00
-- url     : https://prove2.me/theorems/76da6d77-c1a9-401d-be58-920b1c940289
-- title:
--   Whittaker: chi apply
-- statement:
--   The Whittaker construction uses the chi apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerDistribution.lean#L56-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerDistribution.lean#L56-L57

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
variable (ψ₀ : AddChar F ℂ)

theorem GroundTheory.Automorphic.Whittaker.chi_apply (h : NN F n) :
    chi ψ₀ h = psiN ψ₀ (h.1 : GL (Fin n) F) * (psiN ψ₀ (h.2 : GL (Fin n) F))⁻¹ := by sorry
