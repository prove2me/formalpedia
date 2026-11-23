-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_HermitianForm_toSesq_self_mem_range
-- name    : GroundTheory.Automorphic.HermitianForm.toSesq_self_mem_range
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T07:23:19.598046+00:00
-- url     : https://prove2.me/theorems/4d22150e-a757-4f64-b97a-34a55cc9e3ec
-- title:
--   Hermitian Form: to Sesq self mem range
-- statement:
--   The Hermitian Form construction uses the to Sesq self mem range property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HermitianOrthogonal.lean#L120-L122
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HermitianOrthogonal.lean#L120-L122

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

theorem GroundTheory.Automorphic.HermitianForm.toSesq_self_mem_range [Algebra.IsSeparable F E] (h : HermitianForm F E V) (x : V) :
    h.toSesq x x ∈ Set.range (algebraMap F E) := by sorry
