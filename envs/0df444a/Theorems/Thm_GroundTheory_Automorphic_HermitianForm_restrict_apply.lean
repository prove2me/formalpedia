-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_HermitianForm_restrict_apply
-- name    : GroundTheory.Automorphic.HermitianForm.restrict_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:23:18.290594+00:00
-- url     : https://prove2.me/theorems/52ac6d94-022e-41bf-abdc-082afec0fd54
-- title:
--   Hermitian Form: restrict apply
-- statement:
--   The Hermitian Form construction uses the restrict apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HermitianOrthogonal.lean#L271-L273
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HermitianOrthogonal.lean#L271-L273

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

theorem GroundTheory.Automorphic.HermitianForm.restrict_apply (h : HermitianForm F E V) (W W' : Submodule E V)
    (hW : h.IsOrthoCompl W W') (x y : W) :
    (h.restrict W W' hW).toSesq x y = h.toSesq x y := by sorry

attribute [defeq] GroundTheory.Automorphic.HermitianForm.restrict_apply
