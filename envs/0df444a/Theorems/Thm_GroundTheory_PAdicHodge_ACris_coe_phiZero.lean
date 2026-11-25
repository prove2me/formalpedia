-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_ACris_coe_phiZero
-- name    : GroundTheory.PAdicHodge.ACris.coe_phiZero
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T10:01:28.374445+00:00
-- url     : https://prove2.me/theorems/ee73f9d5-2d4b-55f7-871f-5b4e4482f50f
-- title:
--   ACris: coe phi Zero
-- statement:
--   The ACris construction uses the coe phi Zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/FactorizationFactorialLe.lean#L378-L379
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/FactorizationFactorialLe.lean#L378-L379

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_AInfXi
import Definitions.Def_GroundTheory_PAdicHodge_ThetaPlus
import Definitions.Def_GroundTheory_PAdicHodge_FactorizationFactorialLe
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
open _root_.WittVector
open GroundTheory.PAdicHodge.ACris
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
variable {p : ℕ} [hp : Fact p.Prime] [IsPerfectoidField K p]
local notation "θ" => fontaineTheta (normInteger K) p
local notation "𝔸" => Localization.Away (p : AInf K p)
local notation "φ" => WittVector.frobeniusEquiv p (PreTilt (normInteger K) p)

theorem GroundTheory.PAdicHodge.ACris.coe_phiZero (y : ACrisZero K p) : (phiZero K p y : 𝔸) = phiAway K p y := by sorry
