-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_HermitianForm_mul_inv_mem_unitaryGroup
-- name    : GroundTheory.Automorphic.HermitianForm.mul_inv_mem_unitaryGroup
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T02:58:18.225941+00:00
-- url     : https://prove2.me/theorems/dee5a212-0787-54e4-82a9-a0cb661285b3
-- title:
--   Hermitian Form: mul inv mem unitary Group
-- statement:
--   The Hermitian Form construction uses the mul inv mem unitary Group property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/StableConjInvariant.lean#L49-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/StableConjInvariant.lean#L49-L54

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_StableConjTorus
import Definitions.Def_GroundTheory_AutomorphicForms_StableConjInvariant
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
variable {V : Type*} [AddCommGroup V] [Module E V] [FiniteDimensional E V]
open GroundTheory.Automorphic.HermitianForm
variable (h : HermitianForm F E V)
omit [FiniteDimensional E V]

theorem GroundTheory.Automorphic.HermitianForm.mul_inv_mem_unitaryGroup {a b : V ≃ₗ[E] V}
    (hab : h.adjointEquiv a * a = h.adjointEquiv b * b) : b * a⁻¹ ∈ h.unitaryGroup := by sorry
