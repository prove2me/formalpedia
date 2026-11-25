-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Parabolic_isCompl_isotypicPart_isotypicKernel
-- name    : GroundTheory.Automorphic.Parabolic.isCompl_isotypicPart_isotypicKernel
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T13:30:32.832205+00:00
-- url     : https://prove2.me/theorems/16ecc806-1f5e-58ce-b25c-df78d10510fe
-- title:
--   Parabolic: is Compl isotypic Part isotypic Kernel
-- statement:
--   The Parabolic construction uses the is Compl isotypic Part isotypic Kernel property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/CuspidalSplittingIsotypic.lean#L401-L406
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/CuspidalSplittingIsotypic.lean#L401-L406

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

theorem GroundTheory.Automorphic.Parabolic.isCompl_isotypicPart_isotypicKernel :
    IsCompl (isotypicPart π ρ) (isotypicKernel π ρ) := by sorry
