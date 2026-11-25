-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Parabolic_not_surjective_of_le_isotypicKernel
-- name    : GroundTheory.Automorphic.Parabolic.not_surjective_of_le_isotypicKernel
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T13:38:01.21545+00:00
-- url     : https://prove2.me/theorems/f4b7b4f0-6e9e-4820-8143-1645c7dd6605
-- title:
--   Parabolic: not surjective of le isotypic Kernel
-- statement:
--   The Parabolic construction uses the not surjective of le isotypic Kernel property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/CuspidalSplittingIsotypic.lean#L408-L426
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/CuspidalSplittingIsotypic.lean#L408-L426

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

theorem GroundTheory.Automorphic.Parabolic.not_surjective_of_le_isotypicKernel (A : Subrepresentation ρ)
    (hA : A.toSubmodule ≤ isotypicKernel π ρ)
    (p : Representation.IntertwiningMap A.toRepresentation π) : ¬ Surjective p := by sorry
