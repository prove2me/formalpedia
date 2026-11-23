-- Prove2me | Theorems.Thm_GlobalTheory_DiscUniformisation_tendsto_coeff_zero
-- name    : GlobalTheory.DiscUniformisation.tendsto_coeff_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:56:13.838195+00:00
-- url     : https://prove2.me/theorems/f4b30c17-ebe9-40dc-afde-1cb04cb73f5e
-- title:
--   Disc Uniformisation: tendsto coeff zero
-- statement:
--   The Disc Uniformisation construction uses the tendsto coeff zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/TendstoCoeffZero.lean#L7-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/TendstoCoeffZero.lean#L7-L16

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

theorem GlobalTheory.DiscUniformisation.tendsto_coeff_zero {k : ℤ} (f : ModularForm 𝒮ℒ k) :
    Tendsto f atImInfty (𝓝 ((qExpansion 1 f).coeff 0)) := by sorry
