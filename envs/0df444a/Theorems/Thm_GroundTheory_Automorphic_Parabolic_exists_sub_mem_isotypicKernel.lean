-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Parabolic_exists_sub_mem_isotypicKernel
-- name    : GroundTheory.Automorphic.Parabolic.exists_sub_mem_isotypicKernel
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T13:35:51.601819+00:00
-- url     : https://prove2.me/theorems/9b0692f0-a8db-59bf-940d-e38432ddc14f
-- title:
--   Parabolic: exists sub mem isotypic Kernel
-- statement:
--   The Parabolic construction uses the exists sub mem isotypic Kernel property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/CuspidalSplittingIsotypic.lean#L257-L399
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/CuspidalSplittingIsotypic.lean#L257-L399

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_CuspidalSplittingProjective
import Definitions.Def_GroundTheory_AutomorphicForms_CuspidalSplittingIsotypic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Parabolic
open Function Topology
variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ}
variable {V U : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup U] [Module ℂ U]
  {π : Representation ℂ (GL (Fin n) F) V} {ρ : Representation ℂ (GL (Fin n) F) U}
  {ω : GL (Fin n) F → ℂ}
variable [π.IsIrreducible] (hπ : IsSmooth π) (hsc : IsSupercuspidal π)
  (hωπ : HasCentralChar π ω) (hρ : IsSmooth ρ) (hωρ : HasCentralChar ρ ω)
include hπ hsc hωπ hρ hωρ

theorem GroundTheory.Automorphic.Parabolic.exists_sub_mem_isotypicKernel (u : U) :
    ∃ u' ∈ isotypicPart π ρ, u - u' ∈ isotypicKernel π ρ := by sorry
