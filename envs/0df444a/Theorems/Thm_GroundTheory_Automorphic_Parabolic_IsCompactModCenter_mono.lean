-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Parabolic_IsCompactModCenter_mono
-- name    : GroundTheory.Automorphic.Parabolic.IsCompactModCenter.mono
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T12:54:24.087981+00:00
-- url     : https://prove2.me/theorems/60c86174-d07f-5a42-9abd-3d611e111b91
-- title:
--   Is Compact Mod Center: mono
-- statement:
--   The Is Compact Mod Center construction uses the mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/CuspidalSplittingSums.lean#L73-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/CuspidalSplittingSums.lean#L73-L76

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
omit [ValuativeRel F] [IsNonarchimedeanLocalField F]

theorem GroundTheory.Automorphic.Parabolic.IsCompactModCenter.mono {φ ψ : GL (Fin n) F → ℂ} (hφ : IsCompactModCenter φ)
    (h : support ψ ⊆ support φ) : IsCompactModCenter ψ := by sorry
