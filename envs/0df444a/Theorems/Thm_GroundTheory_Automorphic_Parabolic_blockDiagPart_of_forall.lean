-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Parabolic_blockDiagPart_of_forall
-- name    : GroundTheory.Automorphic.Parabolic.blockDiagPart_of_forall
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T23:32:49.817817+00:00
-- url     : https://prove2.me/theorems/1f5e0990-807c-4fc5-a318-eae9cd08316a
-- title:
--   Parabolic: block Diag Part of forall
-- statement:
--   The Parabolic construction uses the block Diag Part of forall property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/InductionParabolicGroups.lean#L47-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/InductionParabolicGroups.lean#L47-L53

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_Iwasawa
import Definitions.Def_GroundTheory_AutomorphicForms_InductionParabolicGroups
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
open Matrix Iwasawa
variable (F : Type*) [Field F] (n : ℕ) {α : Type*} [LinearOrder α] (β : Fin n → α)
variable {F n β}

theorem GroundTheory.Automorphic.Parabolic.blockDiagPart_of_forall {A : Matrix (Fin n) (Fin n) F}
    (hA : ∀ i j, β i ≠ β j → A i j = 0) : blockDiagPart F n β A = A := by sorry
