-- Prove2me | Theorems.Thm_GroundTheory_LocalField_sub_one_le_of_lt
-- name    : GroundTheory.LocalField.sub_one_le_of_lt
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T01:26:43.89953+00:00
-- url     : https://prove2.me/theorems/9f583157-fc9b-47ed-b5e7-3fd5e6de3564
-- title:
--   Local Field: sub one le of lt
-- statement:
--   The Local Field construction uses the sub one le of lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/PadicLogHom.lean#L216-L219
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/PadicLogHom.lean#L216-L219

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
variable (p : ℕ) [hp : Fact p.Prime] [CharP 𝓀[K] p] [CharZero K]
omit [CharP 𝓀[K] p] [CharZero K]

theorem GroundTheory.LocalField.sub_one_le_of_lt {a : ℤ} (ha : (absRamificationIndex K : ℤ) < (p - 1 : ℤ) * a) {b : ℤ}
    (hab : a ≤ b) : (absRamificationIndex K : ℤ) < (p - 1 : ℤ) * b := by sorry
