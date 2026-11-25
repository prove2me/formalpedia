-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_ACris_logCoeff_of_gt
-- name    : GroundTheory.PAdicHodge.ACris.logCoeff_of_gt
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T10:14:34.325786+00:00
-- url     : https://prove2.me/theorems/ae6d24b1-58e4-5614-8e59-b792d13cc1da
-- title:
--   ACris: log Coeff of gt
-- statement:
--   The ACris construction uses the log Coeff of gt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/ACrisPhi.lean#L77-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/ACrisPhi.lean#L77-L78

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

theorem GroundTheory.PAdicHodge.ACris.logCoeff_of_gt {n j : ℕ} (h : p * (n + 1) < j + 1) : logCoeff p n j = 0 := by sorry
