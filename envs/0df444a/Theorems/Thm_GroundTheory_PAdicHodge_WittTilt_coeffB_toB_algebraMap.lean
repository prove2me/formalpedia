-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_WittTilt_coeffB_toB_algebraMap
-- name    : GroundTheory.PAdicHodge.WittTilt.coeffB_toB_algebraMap
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T11:38:01.468696+00:00
-- url     : https://prove2.me/theorems/a3bf8f01-ca6d-4ecb-8b01-df2dd7d71345
-- title:
--   Witt Tilt: coeff B to B algebra Map
-- statement:
--   The Witt Tilt construction uses the coeff B to B algebra Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/BCrisNewtonLift.lean#L162-L164
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/BCrisNewtonLift.lean#L162-L164

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_TiltField
import Definitions.Def_GroundTheory_PAdicHodge_ExtRobbaBounded
import Definitions.Def_GroundTheory_PAdicHodge_KerFontaineThetaCompFrobeniusEquivSymmPow
import Definitions.Def_GroundTheory_PAdicHodge_BCrisNewtonLift
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
open GroundTheory.PAdicHodge.WittTilt
open _root_.WittVector
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
variable {p : ℕ} [hp : Fact p.Prime] [IsPerfectoidField K p]
local notation "𝒪♭" => PreTilt (normInteger K) p
local notation "K♭" => Tilt K NormedField.valuation (normInteger K) normInteger_integers p
local notation "𝔸" => Localization.Away (p : AInf K p)

theorem GroundTheory.PAdicHodge.WittTilt.coeffB_toB_algebraMap (x : AInf K p) :
    (teichLift K p).coeffB (toB K p (algebraMap (AInf K p) 𝔸 x)) = (teichLift K p).zcoeff (incl K p x) := by sorry
