-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_AInf_fontaineTheta_mu
-- name    : GroundTheory.PAdicHodge.AInf.fontaineTheta_mu
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T10:44:16.344391+00:00
-- url     : https://prove2.me/theorems/fcb3ecb9-3244-4103-be51-3dd384bb9f1a
-- title:
--   AInf: fontaine Theta mu
-- statement:
--   The AInf construction uses the fontaine Theta mu property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/AInfXi.lean#L91-L92
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/AInfXi.lean#L91-L92

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_KerFontaineThetaCompFrobeniusEquivSymmPow
import Definitions.Def_GroundTheory_PAdicHodge_AInfXi
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
open WittVector
open GroundTheory GroundTheory.PAdicHodge
open GroundTheory.PAdicHodge.AInf
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
variable {p : ℕ} [hp : Fact p.Prime] [IsPerfectoidField K p]
local notation "𝒪" => normInteger K
local notation "𝒪♭" => PreTilt (normInteger K) p
local notation "θ" => fontaineTheta (normInteger K) p
local notation "φ" => WittVector.frobeniusEquiv p (PreTilt (normInteger K) p)

theorem GroundTheory.PAdicHodge.AInf.fontaineTheta_mu {ε : 𝒪♭} (hε : PreTilt.untilt ε = 1) : θ (mu ε) = 0 := by sorry
