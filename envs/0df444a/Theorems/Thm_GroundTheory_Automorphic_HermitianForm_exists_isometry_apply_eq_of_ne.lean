-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_HermitianForm_exists_isometry_apply_eq_of_ne
-- name    : GroundTheory.Automorphic.HermitianForm.exists_isometry_apply_eq_of_ne
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T23:31:01.47719+00:00
-- url     : https://prove2.me/theorems/45beb464-3402-4b35-9c09-1a209dabcd4d
-- title:
--   Hermitian Form: exists isometry apply eq of ne
-- statement:
--   The Hermitian Form construction uses the exists isometry apply eq of ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HermitianWitt.lean#L97-L118
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HermitianWitt.lean#L97-L118

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HermitianOrthogonal
import Definitions.Def_GroundTheory_AutomorphicForms_HermitianWitt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Automorphic
open Module
variable {F E : Type*} [Field F] [Field E] [Algebra F E] [Algebra.IsQuadraticExtension F E]
variable {V V₁ V₂ : Type*} [AddCommGroup V] [Module E V] [AddCommGroup V₁] [Module E V₁]
  [AddCommGroup V₂] [Module E V₂]
open GroundTheory.Automorphic.HermitianForm

theorem GroundTheory.Automorphic.HermitianForm.exists_isometry_apply_eq_of_ne [FiniteDimensional E V] (h : HermitianForm F E V)
    {x y : V} (hxy : h.toSesq x x = h.toSesq y y) (hd : h.toSesq x x - h.toSesq y x ≠ 0) :
    ∃ g : V ≃ₗ[E] V, (∀ z z', h.toSesq (g z) (g z') = h.toSesq z z') ∧ g x = y := by sorry
