-- Prove2me | Theorems.Thm_GroundTheory_LocalField_modulus_cpow_eq_zpow
-- name    : GroundTheory.LocalField.modulus_cpow_eq_zpow
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T09:38:18.712798+00:00
-- url     : https://prove2.me/theorems/8bf957c8-8a10-4cae-9dc7-f4150d89dd19
-- title:
--   Local Field: modulus cpow eq zpow
-- statement:
--   The Local Field construction uses the modulus cpow eq zpow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LocalZetaShell.lean#L203-L213
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LocalZetaShell.lean#L203-L213

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_LocalFourier
import Definitions.Def_GroundTheory_LocalFields_LocalZetaShell
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.LocalField
open ValuativeRel MeasureTheory Measure Topology Filter
open scoped WithZero NNReal ENNReal Pointwise
variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

theorem GroundTheory.LocalField.modulus_cpow_eq_zpow (u : Kˣ) (s : ℂ) :
    ((modulus (u : K) : ℝ) : ℂ) ^ s = ((residueCard K : ℂ) ^ (-s)) ^ ord (u : K) := by sorry
