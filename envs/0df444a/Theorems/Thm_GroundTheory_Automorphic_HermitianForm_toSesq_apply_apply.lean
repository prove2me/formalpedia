-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_HermitianForm_toSesq_apply_apply
-- name    : GroundTheory.Automorphic.HermitianForm.toSesq_apply_apply
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T01:00:13.994816+00:00
-- url     : https://prove2.me/theorems/eacd00e1-16c8-4d5e-aff7-90ca87a3cd5a
-- title:
--   Hermitian Form: to Sesq apply apply
-- statement:
--   The Hermitian Form construction uses the to Sesq apply apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/StableConjTorus.lean#L146-L148
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/StableConjTorus.lean#L146-L148

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

theorem GroundTheory.Automorphic.HermitianForm.toSesq_apply_apply (g : V ≃ₗ[E] V) (x y : V) :
    h.toSesq (g x) (g y) = h.toSesq ((h.adjointEquiv g * g) x) y := by sorry
