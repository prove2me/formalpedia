-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_HermitianForm_toSesq_adjointEquiv_right
-- name    : GroundTheory.Automorphic.HermitianForm.toSesq_adjointEquiv_right
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T01:04:36.876401+00:00
-- url     : https://prove2.me/theorems/2b80c1b5-4b23-40ea-a9c9-e1fa12e9867a
-- title:
--   Hermitian Form: to Sesq adjoint Equiv right
-- statement:
--   The Hermitian Form construction uses the to Sesq adjoint Equiv right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/StableConjTorus.lean#L111-L113
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/StableConjTorus.lean#L111-L113

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

theorem GroundTheory.Automorphic.HermitianForm.toSesq_adjointEquiv_right (g : V ≃ₗ[E] V) (x y : V) :
    h.toSesq x (h.adjointEquiv g y) = h.toSesq (g x) y := by sorry
