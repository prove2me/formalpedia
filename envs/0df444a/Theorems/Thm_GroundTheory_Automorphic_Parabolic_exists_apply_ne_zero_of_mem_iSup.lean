-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Parabolic_exists_apply_ne_zero_of_mem_iSup
-- name    : GroundTheory.Automorphic.Parabolic.exists_apply_ne_zero_of_mem_iSup
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T13:38:09.684086+00:00
-- url     : https://prove2.me/theorems/a9eaa6b3-7779-4644-a05e-f4e738a5b18c
-- title:
--   Parabolic: exists apply ne zero of mem i Sup
-- statement:
--   The Parabolic construction uses the exists apply ne zero of mem i Sup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/CuspidalSplittingIsotypic.lean#L153-L192
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/CuspidalSplittingIsotypic.lean#L153-L192

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

theorem GroundTheory.Automorphic.Parabolic.exists_apply_ne_zero_of_mem_iSup [π.IsIrreducible] (hπ : IsSmooth π)
    (hsc : IsSupercuspidal π) (hωπ : HasCentralChar π ω) (hρ : IsSmooth ρ)
    (hωρ : HasCentralChar ρ ω) (s : Finset (Representation.IntertwiningMap π ρ)) :
    ∀ y ∈ ⨆ t ∈ s, LinearMap.range (t : Representation.IntertwiningMap π ρ).toLinearMap,
      y ≠ 0 → ∃ Fm : Representation.IntertwiningMap ρ π, Fm y ≠ 0 := by sorry
