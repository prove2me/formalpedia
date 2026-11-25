-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_HermitianForm_adjointEquiv_inv
-- name    : GroundTheory.Automorphic.HermitianForm.adjointEquiv_inv
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T00:59:22.974802+00:00
-- url     : https://prove2.me/theorems/17ee785b-7c48-4991-830a-6cb10d25fa2c
-- title:
--   Hermitian Form: adjoint Equiv inv
-- statement:
--   The Hermitian Form construction uses the adjoint Equiv inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/StableConjTorus.lean#L143-L144
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/StableConjTorus.lean#L143-L144

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

theorem GroundTheory.Automorphic.HermitianForm.adjointEquiv_inv (a : V ≃ₗ[E] V) : h.adjointEquiv a⁻¹ = (h.adjointEquiv a)⁻¹ := by sorry
