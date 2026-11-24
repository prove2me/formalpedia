-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Whittaker_relSpan_le_supportedIn
-- name    : GroundTheory.Automorphic.Whittaker.relSpan_le_supportedIn
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:10:03.138504+00:00
-- url     : https://prove2.me/theorems/2a6c80fe-5093-4cec-9a29-8e8d5df3de4b
-- title:
--   Whittaker: rel Span le supported In
-- statement:
--   The Whittaker construction uses the rel Span le supported In property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerOrbit.lean#L73-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerOrbit.lean#L73-L78

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerLSpace
import Definitions.Def_GroundTheory_AutomorphicForms_SmoothRep
import Definitions.Def_GroundTheory_AutomorphicForms_LocallyProfinite
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerOrbit
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
open Set Topology MulAction
open scoped Pointwise
variable {X : Type*} [TopologicalSpace X] {H : Type*} [Group H] [TopologicalSpace H]
  [MulAction H X] [ContinuousSMul H X]

theorem GroundTheory.Automorphic.Whittaker.relSpan_le_supportedIn (χ : H →* ℂ) {U : Set X}
    (hUinv : ∀ h : H, ∀ x ∈ U, h • x ∈ U) : relSpan χ U ≤ supportedIn U := by sorry
