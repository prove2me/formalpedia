-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Parabolic_valuation_zpow_mul_le
-- name    : GroundTheory.Automorphic.Parabolic.valuation_zpow_mul_le
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T10:09:59.631871+00:00
-- url     : https://prove2.me/theorems/4a35796c-3bd0-4603-9da7-e39e05b82c10
-- title:
--   Parabolic: valuation zpow mul le
-- statement:
--   The Parabolic construction uses the valuation zpow mul le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/InductionParabolicLocal.lean#L24-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/InductionParabolicLocal.lean#L24-L29

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

theorem GroundTheory.Automorphic.Parabolic.valuation_zpow_mul_le {x : F} {k t : ℕ} (hx : (GLnLocal.uniformizer F : F) ^ k * x ∈ 𝒪[F])
    {z : ℤ} (hz : ((k + t : ℕ) : ℤ) ≤ z) :
    valuation F ((GLnLocal.uniformizer F : F) ^ z * x) ≤ valuation F (GLnLocal.uniformizer F : F) ^ t := by sorry
