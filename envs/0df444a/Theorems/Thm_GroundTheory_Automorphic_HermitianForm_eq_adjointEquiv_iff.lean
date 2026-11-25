-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_HermitianForm_eq_adjointEquiv_iff
-- name    : GroundTheory.Automorphic.HermitianForm.eq_adjointEquiv_iff
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T00:59:12.197412+00:00
-- url     : https://prove2.me/theorems/177f9b32-1545-4c5d-9b30-e2e2079d783b
-- title:
--   Hermitian Form: eq adjoint Equiv iff
-- statement:
--   The Hermitian Form construction uses the eq adjoint Equiv iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/StableConjTorus.lean#L115-L121
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/StableConjTorus.lean#L115-L121

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

theorem GroundTheory.Automorphic.HermitianForm.eq_adjointEquiv_iff (g b : V ≃ₗ[E] V) :
    b = h.adjointEquiv g ↔ ∀ y x, h.toSesq (b y) x = h.toSesq y (g x) := by sorry
