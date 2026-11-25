-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Parabolic_elimGL_apply
-- name    : GroundTheory.Automorphic.Parabolic.elimGL_apply
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T11:18:33.5018+00:00
-- url     : https://prove2.me/theorems/451d8c10-7d92-5482-9bd7-ad965bc9f095
-- title:
--   Parabolic: elim GL apply
-- statement:
--   The Parabolic construction uses the elim GL apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/IwahoriFactorization.lean#L91-L93
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/IwahoriFactorization.lean#L91-L93

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_InductionParabolic
import Definitions.Def_GroundTheory_AutomorphicForms_AffineBruhat
import Definitions.Def_GroundTheory_AutomorphicForms_IwahoriFactorization
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
open GroundTheory.Automorphic.Parabolic
open Matrix Iwasawa GLnLocal ValuativeRel Topology Filter Set
variable {F : Type*} [Field F] {n : ℕ} {α : Type*} [LinearOrder α] (β : Fin n → α)
variable {β}
variable (β)
variable {β}
variable (β)
variable {β}

theorem GroundTheory.Automorphic.Parabolic.elimGL_apply (h : Matrix (Fin n) (Fin n) F) (a i k : Fin n) :
    (elimGL β h a : GL (Fin n) F) i k = (1 : Matrix (Fin n) (Fin n) F) i k - elimCol β h a i k := by sorry
