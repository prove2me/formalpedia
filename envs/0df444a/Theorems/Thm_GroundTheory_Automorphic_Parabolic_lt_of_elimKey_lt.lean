-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Parabolic_lt_of_elimKey_lt
-- name    : GroundTheory.Automorphic.Parabolic.lt_of_elimKey_lt
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T11:19:44.215032+00:00
-- url     : https://prove2.me/theorems/7c60ee25-9091-4fe6-8abf-e3739d1096c7
-- title:
--   Parabolic: lt of elim Key lt
-- statement:
--   The Parabolic construction uses the lt of elim Key lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/IwahoriFactorization.lean#L32-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/IwahoriFactorization.lean#L32-L37

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

theorem GroundTheory.Automorphic.Parabolic.lt_of_elimKey_lt {i j : Fin n} (h : elimKey β i < elimKey β j) (hβ : Monotone β) :
    i < j := by sorry
