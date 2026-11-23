-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_HermitianForm_toSesq_smul_right
-- name    : GroundTheory.Automorphic.HermitianForm.toSesq_smul_right
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:22:59.972567+00:00
-- url     : https://prove2.me/theorems/cff8a000-b031-4f94-ad45-6d40743de0a9
-- title:
--   Hermitian Form: to Sesq smul right
-- statement:
--   The Hermitian Form construction uses the to Sesq smul right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HermitianOrthogonal.lean#L98-L100
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HermitianOrthogonal.lean#L98-L100

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

theorem GroundTheory.Automorphic.HermitianForm.toSesq_smul_right (h : HermitianForm F E V) (c : E) (x y : V) :
    h.toSesq x (c • y) = c * h.toSesq x y := by sorry
