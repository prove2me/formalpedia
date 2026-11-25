-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_IsPerfectoidField_coe_normInteger_padicComplex
-- name    : GroundTheory.PAdicHodge.IsPerfectoidField.coe_normInteger_padicComplex
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T13:01:08.12164+00:00
-- url     : https://prove2.me/theorems/34ec7a19-e5b8-4313-93ae-fcb1f9210212
-- title:
--   Is Perfectoid Field: coe norm Integer padic Complex
-- statement:
--   The Is Perfectoid Field construction uses the coe norm Integer padic Complex property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/PerfectoidField.lean#L199-L204
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/PerfectoidField.lean#L199-L204

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_PerfectoidField
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
open GroundTheory GroundTheory.PAdicHodge
open NNReal
open GroundTheory.PAdicHodge.IsPerfectoidField
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]

theorem GroundTheory.PAdicHodge.IsPerfectoidField.coe_normInteger_padicComplex (p : ℕ) [Fact p.Prime] :
    (normInteger ℂ_[p] : Set ℂ_[p]) = (𝓞_ℂ_[p] : Set ℂ_[p]) := by sorry
