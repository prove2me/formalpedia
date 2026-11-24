-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Parabolic_diagGL_inv_conj_apply
-- name    : GroundTheory.Automorphic.Parabolic.diagGL_inv_conj_apply
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T23:34:40.840798+00:00
-- url     : https://prove2.me/theorems/899cadd4-c178-4d8a-9ed0-8275de8d5950
-- title:
--   Parabolic: diag GL inv conj apply
-- statement:
--   The Parabolic construction uses the diag GL inv conj apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/InductionParabolicGroups.lean#L199-L206
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/InductionParabolicGroups.lean#L199-L206

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

theorem GroundTheory.Automorphic.Parabolic.diagGL_inv_conj_apply (d : Fin n → Fˣ) (g : GL (Fin n) F) (i j : Fin n) :
    ((diagGL F n d)⁻¹ * g * diagGL F n d : GL (Fin n) F) i j =
      (((d i)⁻¹ : Fˣ) : F) * g i j * (d j : F) := by sorry
