-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_HermitianForm_toSesq_self_ne_zero_of_eq
-- name    : GroundTheory.Automorphic.HermitianForm.toSesq_self_ne_zero_of_eq
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T23:31:41.780521+00:00
-- url     : https://prove2.me/theorems/4fb2c1f3-d0b0-4b8f-95b1-81780072343c
-- title:
--   Hermitian Form: to Sesq self ne zero of eq
-- statement:
--   The Hermitian Form construction uses the to Sesq self ne zero of eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HermitianWitt.lean#L43-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HermitianWitt.lean#L43-L45

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

theorem GroundTheory.Automorphic.HermitianForm.toSesq_self_ne_zero_of_eq (h : HermitianForm F E V) {v : V} {a : Fˣ}
    (hv : h.toSesq v v = algebraMap F E a) : h.toSesq v v ≠ 0 := by sorry
