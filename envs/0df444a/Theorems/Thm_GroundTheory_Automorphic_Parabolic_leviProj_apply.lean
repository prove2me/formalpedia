-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Parabolic_leviProj_apply
-- name    : GroundTheory.Automorphic.Parabolic.leviProj_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:50:00.232174+00:00
-- url     : https://prove2.me/theorems/c12af958-f5d1-427b-bf11-1376b3d52bd2
-- title:
--   Parabolic: levi Proj apply
-- statement:
--   The Parabolic construction uses the levi Proj apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/InductionParabolicGroups.lean#L112-L114
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/InductionParabolicGroups.lean#L112-L114

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
variable (F n β)
variable {F n β}
variable (F n β)
variable {F n β}

theorem GroundTheory.Automorphic.Parabolic.leviProj_apply (p : blockUpper F n β) (i j : Fin n) :
    ((leviProj F n β p : levi F n β) : GL (Fin n) F) i j =
      if β i = β j then (p : GL (Fin n) F) i j else 0 := by sorry
