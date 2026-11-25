-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_HermitianForm_isOrthoCompl_span_singleton
-- name    : GroundTheory.Automorphic.HermitianForm.isOrthoCompl_span_singleton
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T23:31:47.435809+00:00
-- url     : https://prove2.me/theorems/67951da2-b030-487f-bbfc-0c137ff85238
-- title:
--   Hermitian Form: is Ortho Compl span singleton
-- statement:
--   The Hermitian Form construction uses the is Ortho Compl span singleton property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HermitianOrthogonal.lean#L284-L309
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HermitianOrthogonal.lean#L284-L309

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

theorem GroundTheory.Automorphic.HermitianForm.isOrthoCompl_span_singleton (h : HermitianForm F E V) {v : V}
    (hv : h.toSesq v v ≠ 0) :
    h.IsOrthoCompl (Submodule.span E {v}) (LinearMap.ker (h.toSesq v)) := by sorry
