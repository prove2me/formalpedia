-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Parabolic_zpow_mul_mem
-- name    : GroundTheory.Automorphic.Parabolic.zpow_mul_mem
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T10:13:22.416456+00:00
-- url     : https://prove2.me/theorems/7a57d315-f02d-46a0-8e3e-eb21513b8892
-- title:
--   Parabolic: zpow mul mem
-- statement:
--   The Parabolic construction uses the zpow mul mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/InductionParabolicLocal.lean#L18-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/InductionParabolicLocal.lean#L18-L22

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_InductionParabolicGroups
import Definitions.Def_GroundTheory_AutomorphicForms_MeasuresParabolic
import Definitions.Def_GroundTheory_AutomorphicForms_InductionParabolicLocal
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
variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

theorem GroundTheory.Automorphic.Parabolic.zpow_mul_mem {x : F} {k : ℕ} (hx : (GLnLocal.uniformizer F : F) ^ k * x ∈ 𝒪[F]) {z : ℤ}
    (hz : (k : ℤ) ≤ z) : (GLnLocal.uniformizer F : F) ^ z * x ∈ 𝒪[F] := by sorry
