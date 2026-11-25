-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Parabolic_elimCol_mul_apply
-- name    : GroundTheory.Automorphic.Parabolic.elimCol_mul_apply
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T11:20:40.965745+00:00
-- url     : https://prove2.me/theorems/fa53f714-48a2-4e76-ac67-9e4332ba7b04
-- title:
--   Parabolic: elim Col mul apply
-- statement:
--   The Parabolic construction uses the elim Col mul apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/IwahoriFactorization.lean#L63-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/IwahoriFactorization.lean#L63-L75

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

theorem GroundTheory.Automorphic.Parabolic.elimCol_mul_apply (h : Matrix (Fin n) (Fin n) F) (a i l : Fin n) :
    (elimCol β h a * h) i l = if elimKey β a < elimKey β i then h i a / h a a * h a l else 0 := by sorry
