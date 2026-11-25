-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_HermitianForm_forall_toSesq_eq_iff
-- name    : GroundTheory.Automorphic.HermitianForm.forall_toSesq_eq_iff
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T01:04:12.265954+00:00
-- url     : https://prove2.me/theorems/cbdea987-1a17-4931-b31f-1d8c4819b950
-- title:
--   Hermitian Form: forall to Sesq eq iff
-- statement:
--   The Hermitian Form construction uses the forall to Sesq eq iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/StableConjTorus.lean#L166-L173
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/StableConjTorus.lean#L166-L173

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

theorem GroundTheory.Automorphic.HermitianForm.forall_toSesq_eq_iff (g c : V ≃ₗ[E] V) :
    (∀ x y, h.toSesq (g x) (g y) = h.toSesq (c x) y) ↔ h.adjointEquiv g * g = c := by sorry
