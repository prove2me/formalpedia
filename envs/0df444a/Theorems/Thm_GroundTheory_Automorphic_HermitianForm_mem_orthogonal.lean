-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_HermitianForm_mem_orthogonal
-- name    : GroundTheory.Automorphic.HermitianForm.mem_orthogonal
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T23:32:00.555049+00:00
-- url     : https://prove2.me/theorems/d7ede75c-86dd-40d0-837a-c04febaab3e2
-- title:
--   Hermitian Form: mem orthogonal
-- statement:
--   The Hermitian Form construction uses the mem orthogonal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HermitianWitt.lean#L250-L251
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HermitianWitt.lean#L250-L251

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

theorem GroundTheory.Automorphic.HermitianForm.mem_orthogonal (h : HermitianForm F E V) (U : Submodule E V) (y : V) :
    y ∈ h.orthogonal U ↔ ∀ x ∈ U, h.toSesq x y = 0 := by sorry
