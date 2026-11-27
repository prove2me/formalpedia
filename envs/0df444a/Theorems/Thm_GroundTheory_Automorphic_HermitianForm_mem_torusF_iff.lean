-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_HermitianForm_mem_torusF_iff
-- name    : GroundTheory.Automorphic.HermitianForm.mem_torusF_iff
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T12:54:08.060441+00:00
-- url     : https://prove2.me/theorems/319ae226-d4ab-48c2-a1d4-fb821258b1b1
-- title:
--   Hermitian Form: mem torus F iff
-- statement:
--   The Hermitian Form construction uses the mem torus F iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/StableConjInvariant.lean#L95-L100
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/StableConjInvariant.lean#L95-L100

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_StableConjTorus
import Definitions.Def_GroundTheory_AutomorphicForms_StableConjInvariant
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open Module
variable {F E : Type*} [Field F] [Field E] [Algebra F E] [Algebra.IsQuadraticExtension F E]
variable {V : Type*} [AddCommGroup V] [Module E V] [FiniteDimensional E V]
open GroundTheory.Automorphic.HermitianForm
variable (h : HermitianForm F E V)
variable (γ : h.unitaryGroup) [Fact (IsRegularSemisimple (γ : V ≃ₗ[E] V))]

theorem GroundTheory.Automorphic.HermitianForm.mem_torusF_iff (t : TorusE (γ : V ≃ₗ[E] V)) :
    t ∈ h.torusF γ ↔ t.val ∈ h.unitaryGroup := by sorry
