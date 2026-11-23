-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_HermitianForm_isometric_prod_comm
-- name    : GroundTheory.Automorphic.HermitianForm.isometric_prod_comm
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:55:51.910605+00:00
-- url     : https://prove2.me/theorems/adb57175-588d-4c0a-988d-1871befc293e
-- title:
--   Hermitian Form: isometric prod comm
-- statement:
--   The Hermitian Form construction uses the isometric prod comm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HermitianOrthogonal.lean#L194-L198
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HermitianOrthogonal.lean#L194-L198

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

theorem GroundTheory.Automorphic.HermitianForm.isometric_prod_comm (h : HermitianForm F E V) (h' : HermitianForm F E V') :
    Isometric (h.prod h') (h'.prod h) := by sorry
