-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Parabolic_diagGL_conj_apply
-- name    : GroundTheory.Automorphic.Parabolic.diagGL_conj_apply
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T11:01:42.359472+00:00
-- url     : https://prove2.me/theorems/06110055-f33d-4078-b8de-8dfc9f68719f
-- title:
--   Parabolic: diag GL conj apply
-- statement:
--   The Parabolic construction uses the diag GL conj apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/InductionParabolicGroups.lean#L189-L196
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/InductionParabolicGroups.lean#L189-L196

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
variable (F n β)
variable {F n β}
variable (F n)

theorem GroundTheory.Automorphic.Parabolic.diagGL_conj_apply (d : Fin n → Fˣ) (g : GL (Fin n) F) (i j : Fin n) :
    (diagGL F n d * g * (diagGL F n d)⁻¹ : GL (Fin n) F) i j =
      (d i : F) * g i j * ((d j)⁻¹ : Fˣ) := by sorry
