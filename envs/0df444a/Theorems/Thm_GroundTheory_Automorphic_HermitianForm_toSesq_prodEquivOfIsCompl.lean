-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_HermitianForm_toSesq_prodEquivOfIsCompl
-- name    : GroundTheory.Automorphic.HermitianForm.toSesq_prodEquivOfIsCompl
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T23:31:45.840781+00:00
-- url     : https://prove2.me/theorems/c6d7c35e-b936-4303-95c3-c357517ddaef
-- title:
--   Hermitian Form: to Sesq prod Equiv Of Is Compl
-- statement:
--   The Hermitian Form construction uses the to Sesq prod Equiv Of Is Compl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HermitianWitt.lean#L283-L291
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HermitianWitt.lean#L283-L291

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

theorem GroundTheory.Automorphic.HermitianForm.toSesq_prodEquivOfIsCompl (h : HermitianForm F E V) {W W' : Submodule E V}
    (hW : h.IsOrthoCompl W W') (p q : W × W') :
    h.toSesq (Submodule.prodEquivOfIsCompl W W' hW.1 p)
      (Submodule.prodEquivOfIsCompl W W' hW.1 q) =
      h.toSesq p.1 q.1 + h.toSesq p.2 q.2 := by sorry
