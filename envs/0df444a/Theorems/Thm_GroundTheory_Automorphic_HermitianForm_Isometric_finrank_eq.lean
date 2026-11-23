-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_HermitianForm_Isometric_finrank_eq
-- name    : GroundTheory.Automorphic.HermitianForm.Isometric.finrank_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:54:57.335369+00:00
-- url     : https://prove2.me/theorems/85582ad8-6bbf-4e3e-aa7f-e1d7c9b5bcae
-- title:
--   Isometric: finrank eq
-- statement:
--   The Isometric construction uses the finrank eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HermitianOrthogonal.lean#L143-L146
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HermitianOrthogonal.lean#L143-L146

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
open GroundTheory.Automorphic.HermitianForm.Isometric

theorem GroundTheory.Automorphic.HermitianForm.Isometric.finrank_eq {h : HermitianForm F E V} {h' : HermitianForm F E V'} (H : Isometric h h') :
    finrank E V = finrank E V' := by sorry
