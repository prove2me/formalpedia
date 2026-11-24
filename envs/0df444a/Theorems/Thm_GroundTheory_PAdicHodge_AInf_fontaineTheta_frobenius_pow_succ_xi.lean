-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_AInf_fontaineTheta_frobenius_pow_succ_xi
-- name    : GroundTheory.PAdicHodge.AInf.fontaineTheta_frobenius_pow_succ_xi
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T11:02:06.737101+00:00
-- url     : https://prove2.me/theorems/8cd7309a-fbea-4665-b599-07f03fea1391
-- title:
--   AInf: fontaine Theta frobenius pow succ xi
-- statement:
--   The AInf construction uses the fontaine Theta frobenius pow succ xi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/FontaineLemmaAInf.lean#L20-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/FontaineLemmaAInf.lean#L20-L24

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_AInfXi
import Definitions.Def_GroundTheory_PAdicHodge_AInfTopology
import Definitions.Def_GroundTheory_PAdicHodge_FontaineLemmaAInf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.PAdicHodge
open GroundTheory.PAdicHodge.AInf
open _root_.WittVector
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
variable {p : ℕ} [hp : Fact p.Prime] [IsPerfectoidField K p]
local notation "𝒪" => normInteger K
local notation "𝒪♭" => PreTilt (normInteger K) p
local notation "θ" => fontaineTheta (normInteger K) p
local notation "φ" => WittVector.frobeniusEquiv p (PreTilt (normInteger K) p)

theorem GroundTheory.PAdicHodge.AInf.fontaineTheta_frobenius_pow_succ_xi {ε : 𝒪♭} (hε : PreTilt.untilt ε = 1) (n : ℕ) :
    θ ((φ ^ (n + 1)) (xi ε)) = p := by sorry
