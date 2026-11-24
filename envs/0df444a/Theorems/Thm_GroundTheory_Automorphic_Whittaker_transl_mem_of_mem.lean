-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Whittaker_transl_mem_of_mem
-- name    : GroundTheory.Automorphic.Whittaker.transl_mem_of_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:13:18.309632+00:00
-- url     : https://prove2.me/theorems/b9ed0485-c774-4dfb-aeec-7bd2d97519e5
-- title:
--   Whittaker: transl mem of mem
-- statement:
--   The Whittaker construction uses the transl mem of mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerOrbit.lean#L262-L270
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerOrbit.lean#L262-L270

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
variable {X : Type*} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
  [TotallyDisconnectedSpace X]
  {H : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [LocallyCompactSpace H]
  [T2Space H] [TotallyDisconnectedSpace H] [SigmaCompactSpace H]
  [MulAction H X] [ContinuousSMul H X]
variable {U C : Set X} {x₀ : X}
omit [LocallyCompactSpace X] [TotallyDisconnectedSpace X] [IsTopologicalGroup H]
  [LocallyCompactSpace H] [T2Space H] [TotallyDisconnectedSpace H] [SigmaCompactSpace H] [T2Space X]
  [TopologicalSpace H] [ContinuousSMul H X]

theorem GroundTheory.Automorphic.Whittaker.transl_mem_of_mem (χ : H →* ℂ)
    {W : Submodule ℂ (X → ℂ)} (hWU : W ≤ supportedIn U) (hW : relSpan χ U ≤ W) (h : H)
    {f : X → ℂ} (hf : f ∈ W ⊔ (supportedIn U ⊓ vanishingOn C)) :
    transl h f ∈ W ⊔ (supportedIn U ⊓ vanishingOn C) := by sorry
