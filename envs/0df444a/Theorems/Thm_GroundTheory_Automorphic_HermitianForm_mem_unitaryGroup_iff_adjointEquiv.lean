-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_HermitianForm_mem_unitaryGroup_iff_adjointEquiv
-- name    : GroundTheory.Automorphic.HermitianForm.mem_unitaryGroup_iff_adjointEquiv
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T00:59:36.145198+00:00
-- url     : https://prove2.me/theorems/3060677e-8563-4480-8ac7-51e3250abb23
-- title:
--   Hermitian Form: mem unitary Group iff adjoint Equiv
-- statement:
--   The Hermitian Form construction uses the mem unitary Group iff adjoint Equiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/StableConjTorus.lean#L162-L164
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/StableConjTorus.lean#L162-L164

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HermitianOrthogonal
import Definitions.Def_GroundTheory_AutomorphicForms_StableConjCyclic
import Definitions.Def_GroundTheory_AutomorphicForms_StableConjTorus
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open Module
variable {F E : Type*} [Field F] [Field E] [Algebra F E] [Algebra.IsQuadraticExtension F E]
variable {V : Type*} [AddCommGroup V] [Module E V]
open GroundTheory.Automorphic.HermitianForm
variable (h : HermitianForm F E V)

theorem GroundTheory.Automorphic.HermitianForm.mem_unitaryGroup_iff_adjointEquiv (g : V ≃ₗ[E] V) :
    g ∈ h.unitaryGroup ↔ h.adjointEquiv g = g⁻¹ := by sorry
