-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_HermitianForm_exists_apply_self_ne_zero
-- name    : GroundTheory.Automorphic.HermitianForm.exists_apply_self_ne_zero
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T07:22:41.307113+00:00
-- url     : https://prove2.me/theorems/2c4f647d-9af8-43d4-a739-51bb83ca8f36
-- title:
--   Hermitian Form: exists apply self ne zero
-- statement:
--   The Hermitian Form construction uses the exists apply self ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HermitianOrthogonal.lean#L315-L333
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HermitianOrthogonal.lean#L315-L333

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
variable [Algebra.IsSeparable F E]

theorem GroundTheory.Automorphic.HermitianForm.exists_apply_self_ne_zero (h : HermitianForm F E V) [Nontrivial V] :
    ∃ x, h.toSesq x x ≠ 0 := by sorry
