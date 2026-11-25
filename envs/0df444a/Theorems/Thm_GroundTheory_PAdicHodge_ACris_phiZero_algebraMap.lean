-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_ACris_phiZero_algebraMap
-- name    : GroundTheory.PAdicHodge.ACris.phiZero_algebraMap
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T10:03:30.226661+00:00
-- url     : https://prove2.me/theorems/9ba7632f-82c7-4226-b325-59ec83fd3b2b
-- title:
--   ACris: phi Zero algebra Map
-- statement:
--   The ACris construction uses the phi Zero algebra Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/FactorizationFactorialLe.lean#L381-L384
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/FactorizationFactorialLe.lean#L381-L384

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

theorem GroundTheory.PAdicHodge.ACris.phiZero_algebraMap (x : AInf K p) :
    phiZero K p (algebraMap (AInf K p) (ACrisZero K p) x) =
      algebraMap (AInf K p) (ACrisZero K p) (φ x) := by sorry
