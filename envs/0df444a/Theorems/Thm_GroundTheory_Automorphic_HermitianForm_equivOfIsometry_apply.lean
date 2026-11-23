-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_HermitianForm_equivOfIsometry_apply
-- name    : GroundTheory.Automorphic.HermitianForm.equivOfIsometry_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:04:02.909812+00:00
-- url     : https://prove2.me/theorems/3ad8bb78-d14a-4f7e-a075-d6d03223f1e2
-- title:
--   Hermitian Form: equiv Of Isometry apply
-- statement:
--   The Hermitian Form construction uses the equiv Of Isometry apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HermitianWitt.lean#L93-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HermitianWitt.lean#L93-L95

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

theorem GroundTheory.Automorphic.HermitianForm.equivOfIsometry_apply [FiniteDimensional E V] (h : HermitianForm F E V) (f : V →ₗ[E] V)
    (hf : ∀ x y, h.toSesq (f x) (f y) = h.toSesq x y) (x : V) :
    h.equivOfIsometry f hf x = f x := by sorry

attribute [defeq] GroundTheory.Automorphic.HermitianForm.equivOfIsometry_apply
