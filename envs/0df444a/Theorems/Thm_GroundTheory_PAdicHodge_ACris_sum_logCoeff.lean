-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_ACris_sum_logCoeff
-- name    : GroundTheory.PAdicHodge.ACris.sum_logCoeff
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T10:16:49.510992+00:00
-- url     : https://prove2.me/theorems/b5bb5b37-4750-4c66-a3fe-31902ed70228
-- title:
--   ACris: sum log Coeff
-- statement:
--   The ACris construction uses the sum log Coeff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/ACrisPhi.lean#L89-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/ACrisPhi.lean#L89-L91

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_ACrisLog
import Definitions.Def_GroundTheory_PAdicHodge_LogPowSeries
import Definitions.Def_GroundTheory_PAdicHodge_ACrisPhi
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
open _root_.WittVector Polynomial
open GroundTheory.PAdicHodge.ACris
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
variable {p : ℕ} [hp : Fact p.Prime] [IsPerfectoidField K p]
local notation "θ" => fontaineTheta (normInteger K) p
local notation "𝔸" => Localization.Away (p : AInf K p)
omit hp

theorem GroundTheory.PAdicHodge.ACris.sum_logCoeff (j : ℕ) :
    ∑ n ∈ Finset.range (j + 1), logCoeff p n j = (-1) ^ j * p * j.factorial := by sorry
