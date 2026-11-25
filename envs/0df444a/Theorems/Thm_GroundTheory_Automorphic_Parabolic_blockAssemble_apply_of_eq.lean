-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Parabolic_blockAssemble_apply_of_eq
-- name    : GroundTheory.Automorphic.Parabolic.blockAssemble_apply_of_eq
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T11:31:00.808194+00:00
-- url     : https://prove2.me/theorems/07636f73-c04c-5915-b6c3-09a02d56056b
-- title:
--   Parabolic: block Assemble apply of eq
-- statement:
--   The Parabolic construction uses the block Assemble apply of eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/LeviCartan.lean#L67-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/LeviCartan.lean#L67-L71

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_AdmissibleInduction
import Definitions.Def_GroundTheory_AutomorphicForms_Cartan
import Definitions.Def_GroundTheory_AutomorphicForms_LeviCartan
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
open Matrix Iwasawa GLnLocal ValuativeRel
variable {n : ℕ} {α : Type*} [LinearOrder α] (β : Fin n → α)
variable (R : Type*) [CommRing R]
variable {β R}

theorem GroundTheory.Automorphic.Parabolic.blockAssemble_apply_of_eq (X : ∀ a : Set.range β, Matrix (Fiber β a) (Fiber β a) R)
    {i j : Fin n} {a : Set.range β} (hi : blockOf β i = a) (hj : blockOf β j = a) :
    blockAssemble β R X i j = X a ⟨i, hi⟩ ⟨j, hj⟩ := by sorry
