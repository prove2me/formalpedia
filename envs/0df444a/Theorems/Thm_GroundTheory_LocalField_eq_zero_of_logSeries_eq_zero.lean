-- Prove2me | Theorems.Thm_GroundTheory_LocalField_eq_zero_of_logSeries_eq_zero
-- name    : GroundTheory.LocalField.eq_zero_of_logSeries_eq_zero
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T01:26:31.226673+00:00
-- url     : https://prove2.me/theorems/38d6ece6-8f7e-4e62-9a94-b369cba60d60
-- title:
--   Local Field: eq zero of log Series eq zero
-- statement:
--   The Local Field construction uses the eq zero of log Series eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/PadicLogHom.lean#L221-L232
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/PadicLogHom.lean#L221-L232

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

theorem GroundTheory.LocalField.eq_zero_of_logSeries_eq_zero {r : ℤ} (hr : (absRamificationIndex K : ℤ) < (p - 1 : ℤ) * r)
    {x : K} (hx : x ∈ valBall K r) (h : logSeries x = 0) : x = 0 := by sorry
