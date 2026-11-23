-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_HermitianForm_toSesq_smul_left
-- name    : GroundTheory.Automorphic.HermitianForm.toSesq_smul_left
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:23:15.266486+00:00
-- url     : https://prove2.me/theorems/9a0fd4f5-6743-4e1c-a729-56fedbc1b96b
-- title:
--   Hermitian Form: to Sesq smul left
-- statement:
--   The Hermitian Form construction uses the to Sesq smul left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HermitianOrthogonal.lean#L94-L96
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HermitianOrthogonal.lean#L94-L96

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HermitianSpaces
import Definitions.Def_GroundTheory_AutomorphicForms_HermitianOrthogonal
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
variable {V V' V'' : Type*} [AddCommGroup V] [Module E V] [AddCommGroup V'] [Module E V']
  [AddCommGroup V''] [Module E V'']
open GroundTheory.Automorphic.HermitianForm

theorem GroundTheory.Automorphic.HermitianForm.toSesq_smul_left (h : HermitianForm F E V) (c : E) (x y : V) :
    h.toSesq (c • x) y = conj F E c * h.toSesq x y := by sorry
