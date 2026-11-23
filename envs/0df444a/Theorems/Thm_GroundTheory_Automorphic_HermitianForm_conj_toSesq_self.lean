-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_HermitianForm_conj_toSesq_self
-- name    : GroundTheory.Automorphic.HermitianForm.conj_toSesq_self
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:55:00.166862+00:00
-- url     : https://prove2.me/theorems/08a1918d-b511-4a3c-aeca-1a1dcd099a85
-- title:
--   Hermitian Form: conj to Sesq self
-- statement:
--   The Hermitian Form construction uses the conj to Sesq self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HermitianOrthogonal.lean#L116-L118
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HermitianOrthogonal.lean#L116-L118

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

theorem GroundTheory.Automorphic.HermitianForm.conj_toSesq_self (h : HermitianForm F E V) (x : V) :
    conj F E (h.toSesq x x) = h.toSesq x x := by sorry
