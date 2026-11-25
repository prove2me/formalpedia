-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_AInf_isAdicComplete_p
-- name    : GroundTheory.PAdicHodge.AInf.isAdicComplete_p
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T13:00:49.066955+00:00
-- url     : https://prove2.me/theorems/28938957-5ee3-5751-b089-ce9776b24998
-- title:
--   AInf: is Adic Complete p
-- statement:
--   The AInf construction uses the is Adic Complete p property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/AInfTopology.lean#L268-L269
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/AInfTopology.lean#L268-L269

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_KerFontaineThetaCompFrobeniusEquivSymmPow
import Definitions.Def_GroundTheory_PAdicHodge_AInfTopology
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
open WittVector Filter Topology
open GroundTheory GroundTheory.PAdicHodge
open GroundTheory.PAdicHodge.AInf
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
variable {p : ℕ} [hp : Fact p.Prime] [IsPerfectoidField K p]
local notation "𝒪♭" => PreTilt (normInteger K) p

theorem GroundTheory.PAdicHodge.AInf.isAdicComplete_p : IsAdicComplete (Ideal.span {(p : AInf K p)}) (AInf K p) := by sorry
