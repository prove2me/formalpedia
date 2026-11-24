-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_HermitianForm_toSesq_quasiReflection
-- name    : GroundTheory.Automorphic.HermitianForm.toSesq_quasiReflection
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T23:31:47.065522+00:00
-- url     : https://prove2.me/theorems/e63ae78d-c5f1-4145-a2de-645eb26078e4
-- title:
--   Hermitian Form: to Sesq quasi Reflection
-- statement:
--   The Hermitian Form construction uses the to Sesq quasi Reflection property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HermitianWitt.lean#L76-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HermitianWitt.lean#L76-L81

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

theorem GroundTheory.Automorphic.HermitianForm.toSesq_quasiReflection (h : HermitianForm F E V) {w : V} {c : E}
    (hc : c + conj F E c = c * conj F E c * h.toSesq w w) (z z' : V) :
    h.toSesq (h.quasiReflection w c z) (h.quasiReflection w c z') = h.toSesq z z' := by sorry
