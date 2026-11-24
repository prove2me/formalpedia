-- Prove2me | Theorems.Thm_GlobalTheory_DiscUniformisation_g_eq
-- name    : GlobalTheory.DiscUniformisation.g_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:56:13.076272+00:00
-- url     : https://prove2.me/theorems/6cd83879-8206-493c-ae0e-2c3871a4c4a0
-- title:
--   Disc Uniformisation: g eq
-- statement:
--   The Disc Uniformisation construction uses the g eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/TendstoCoeffZero.lean#L199-L213
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/TendstoCoeffZero.lean#L199-L213

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_TendstoCoeffZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open UpperHalfPlane ModularForm MatrixGroups EisensteinSeries Filter Topology
open GlobalTheory GlobalTheory.DiscUniformisation

theorem GlobalTheory.DiscUniformisation.g_eq (L : PeriodPair) (z : ℍ) (hz : L.ω₁ = L.ω₂ * z) :
    L.g₂ = 4 / 3 * ((Real.pi * L.ω₂⁻¹) ^ 4 * E₄ z) ∧
      L.g₃ = 8 / 27 * ((Real.pi * L.ω₂⁻¹) ^ 6 * E₆ z) := by sorry
