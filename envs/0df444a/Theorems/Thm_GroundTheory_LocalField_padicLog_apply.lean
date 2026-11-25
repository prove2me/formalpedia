-- Prove2me | Theorems.Thm_GroundTheory_LocalField_padicLog_apply
-- name    : GroundTheory.LocalField.padicLog_apply
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T01:26:38.532208+00:00
-- url     : https://prove2.me/theorems/8828b9a1-3e99-4ec8-829a-ca6aedff5c3b
-- title:
--   Local Field: padic Log apply
-- statement:
--   The Local Field construction uses the padic Log apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/PadicLogHom.lean#L251-L253
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/PadicLogHom.lean#L251-L253

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_PadicLogSeries
import Definitions.Def_GroundTheory_LocalFields_PadicLogHom
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.LocalField
open ValuativeRel IsLocalRing Topology Filter
open scoped WithZero
variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable (K) [CharZero K]
variable {K}

theorem GroundTheory.LocalField.padicLog_apply (u : Additive (unitFiltrationUnits K 1)) :
    padicLog K u = logSeries ((((Additive.toMul u : unitFiltrationUnits K 1) : Kˣ) : K) - 1) := by sorry
