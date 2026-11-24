-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_HermitianForm_isometric_of_prod_isometric_prod
-- name    : GroundTheory.Automorphic.HermitianForm.isometric_of_prod_isometric_prod
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T23:31:02.969824+00:00
-- url     : https://prove2.me/theorems/6f5694f1-9e68-49ed-ad12-61a1e93f5f5d
-- title:
--   Hermitian Form: isometric of prod isometric prod
-- statement:
--   The Hermitian Form construction uses the isometric of prod isometric prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HermitianWitt.lean#L210-L242
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HermitianWitt.lean#L210-L242

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

theorem GroundTheory.Automorphic.HermitianForm.isometric_of_prod_isometric_prod [Algebra.IsSeparable F E] [FiniteDimensional E V₂]
    [FiniteDimensional E V] (h₁ : HermitianForm F E V₁) (h₂ : HermitianForm F E V₂)
    (h : HermitianForm F E V) (H : Isometric (h₁.prod h) (h₂.prod h)) : Isometric h₁ h₂ := by sorry
