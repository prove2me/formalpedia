-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_HermitianForm_exists_isometry_apply_eq
-- name    : GroundTheory.Automorphic.HermitianForm.exists_isometry_apply_eq
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T23:31:51.087064+00:00
-- url     : https://prove2.me/theorems/a3bf63d1-e6e2-49ef-97fa-7d61d1f4582f
-- title:
--   Hermitian Form: exists isometry apply eq
-- statement:
--   The Hermitian Form construction uses the exists isometry apply eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HermitianWitt.lean#L120-L145
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HermitianWitt.lean#L120-L145

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

theorem GroundTheory.Automorphic.HermitianForm.exists_isometry_apply_eq [Algebra.IsSeparable F E] [FiniteDimensional E V]
    (h : HermitianForm F E V) {x y : V} (hxy : h.toSesq x x = h.toSesq y y)
    (hx : h.toSesq x x ≠ 0) :
    ∃ g : V ≃ₗ[E] V, (∀ z z', h.toSesq (g z) (g z') = h.toSesq z z') ∧ g x = y := by sorry
