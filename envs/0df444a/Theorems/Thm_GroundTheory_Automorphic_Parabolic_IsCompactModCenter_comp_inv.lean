-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Parabolic_IsCompactModCenter_comp_inv
-- name    : GroundTheory.Automorphic.Parabolic.IsCompactModCenter.comp_inv
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T12:02:04.687749+00:00
-- url     : https://prove2.me/theorems/10ada20d-900c-4915-9ee5-7d2906c3e139
-- title:
--   Is Compact Mod Center: comp inv
-- statement:
--   The Is Compact Mod Center construction uses the comp inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/CuspidalSplittingSums.lean#L78-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/CuspidalSplittingSums.lean#L78-L87

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_SupercuspidalCoefficients
import Definitions.Def_GroundTheory_AutomorphicForms_CuspidalSplittingSums
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Parabolic
open Function
open scoped Pointwise
variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ}

theorem GroundTheory.Automorphic.Parabolic.IsCompactModCenter.comp_inv {φ : GL (Fin n) F → ℂ} (hφ : IsCompactModCenter φ) :
    IsCompactModCenter fun g => φ g⁻¹ := by sorry
