-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_ACris_factorial_dvd_logCoeff
-- name    : GroundTheory.PAdicHodge.ACris.factorial_dvd_logCoeff
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T10:17:03.127653+00:00
-- url     : https://prove2.me/theorems/c8c5cbd8-ee63-4ae3-b5cc-bb42a8bc66aa
-- title:
--   ACris: factorial dvd log Coeff
-- statement:
--   The ACris construction uses the factorial dvd log Coeff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/ACrisPhi.lean#L81-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/ACrisPhi.lean#L81-L86

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

theorem GroundTheory.PAdicHodge.ACris.factorial_dvd_logCoeff (n j : ℕ) : (n.factorial : ℤ) ∣ logCoeff p n j := by sorry
