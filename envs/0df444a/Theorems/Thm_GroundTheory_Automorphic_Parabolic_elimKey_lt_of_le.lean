-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Parabolic_elimKey_lt_of_le
-- name    : GroundTheory.Automorphic.Parabolic.elimKey_lt_of_le
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T11:20:00.690135+00:00
-- url     : https://prove2.me/theorems/d66bd3ed-b2b7-416f-bc60-c19a9bc334e5
-- title:
--   Parabolic: elim Key lt of le
-- statement:
--   The Parabolic construction uses the elim Key lt of le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/IwahoriFactorization.lean#L39-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/IwahoriFactorization.lean#L39-L41

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

theorem GroundTheory.Automorphic.Parabolic.elimKey_lt_of_le {i j : Fin n} (h : elimKey β i ≤ elimKey β j) (hij : i ≠ j) :
    elimKey β i < elimKey β j := by sorry
