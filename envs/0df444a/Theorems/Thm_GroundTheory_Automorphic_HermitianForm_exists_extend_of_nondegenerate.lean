-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_HermitianForm_exists_extend_of_nondegenerate
-- name    : GroundTheory.Automorphic.HermitianForm.exists_extend_of_nondegenerate
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T23:30:48.15168+00:00
-- url     : https://prove2.me/theorems/6b377895-4945-400d-aa98-4b44626c4dc9
-- title:
--   Hermitian Form: exists extend of nondegenerate
-- statement:
--   The Hermitian Form construction uses the exists extend of nondegenerate property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HermitianWitt.lean#L319-L335
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HermitianWitt.lean#L319-L335

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

theorem GroundTheory.Automorphic.HermitianForm.exists_extend_of_nondegenerate [Algebra.IsSeparable F E] [FiniteDimensional E V]
    (h : HermitianForm F E V) {U₁ U₂ : Submodule E V}
    (hU : ∀ u ∈ U₁, (∀ u' ∈ U₁, h.toSesq u u' = 0) → u = 0) (φ : U₁ ≃ₗ[E] U₂)
    (hφ : ∀ x y : U₁, h.toSesq (φ x) (φ y) = h.toSesq x y) :
    ∃ g : V ≃ₗ[E] V, (∀ x y, h.toSesq (g x) (g y) = h.toSesq x y) ∧ ∀ x : U₁, g x = φ x := by sorry
