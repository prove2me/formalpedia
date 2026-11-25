-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_HermitianForm_isOrthoCompl_orthogonal
-- name    : GroundTheory.Automorphic.HermitianForm.isOrthoCompl_orthogonal
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T23:32:01.490056+00:00
-- url     : https://prove2.me/theorems/fe2cb05f-e96b-4f23-9fbe-6f97fb8111eb
-- title:
--   Hermitian Form: is Ortho Compl orthogonal
-- statement:
--   The Hermitian Form construction uses the is Ortho Compl orthogonal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HermitianWitt.lean#L253-L281
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HermitianWitt.lean#L253-L281

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

theorem GroundTheory.Automorphic.HermitianForm.isOrthoCompl_orthogonal [FiniteDimensional E V] (h : HermitianForm F E V)
    (U : Submodule E V) (hU : ∀ u ∈ U, (∀ u' ∈ U, h.toSesq u u' = 0) → u = 0) :
    h.IsOrthoCompl U (h.orthogonal U) := by sorry
