-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Whittaker_sub_mem_relSpan
-- name    : GroundTheory.Automorphic.Whittaker.sub_mem_relSpan
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:09:53.579622+00:00
-- url     : https://prove2.me/theorems/dfe6be58-2a7f-4d0f-88f1-6c6c5dbb5370
-- title:
--   Whittaker: sub mem rel Span
-- statement:
--   The Whittaker construction uses the sub mem rel Span property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerOrbit.lean#L69-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerOrbit.lean#L69-L71

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
omit [TopologicalSpace H] [ContinuousSMul H X]

theorem GroundTheory.Automorphic.Whittaker.sub_mem_relSpan (χ : H →* ℂ) {U : Set X} (h : H) {f : X → ℂ} (hf : f ∈ supportedIn U) :
    transl h f - χ h • f ∈ relSpan χ U := by sorry
