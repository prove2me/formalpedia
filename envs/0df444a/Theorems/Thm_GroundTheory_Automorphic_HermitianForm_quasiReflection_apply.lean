-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_HermitianForm_quasiReflection_apply
-- name    : GroundTheory.Automorphic.HermitianForm.quasiReflection_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:03:22.724541+00:00
-- url     : https://prove2.me/theorems/9fbc8755-4458-4d44-a47e-16cc0022991f
-- title:
--   Hermitian Form: quasi Reflection apply
-- statement:
--   The Hermitian Form construction uses the quasi Reflection apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HermitianWitt.lean#L72-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HermitianWitt.lean#L72-L74

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

theorem GroundTheory.Automorphic.HermitianForm.quasiReflection_apply (h : HermitianForm F E V) (w : V) (c : E) (z : V) :
    h.quasiReflection w c z = z - (c * h.toSesq w z) • w := by sorry
