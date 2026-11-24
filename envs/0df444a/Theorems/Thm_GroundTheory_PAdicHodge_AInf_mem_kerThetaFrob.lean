-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_AInf_mem_kerThetaFrob
-- name    : GroundTheory.PAdicHodge.AInf.mem_kerThetaFrob
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T10:52:50.123905+00:00
-- url     : https://prove2.me/theorems/69aae4f6-a701-4906-9a8a-8347084705c5
-- title:
--   AInf: mem ker Theta Frob
-- statement:
--   The AInf construction uses the mem ker Theta Frob property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/FontaineLemmaAInf.lean#L47-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/FontaineLemmaAInf.lean#L47-L49

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

theorem GroundTheory.PAdicHodge.AInf.mem_kerThetaFrob {a : AInf K p} : a ∈ kerThetaFrob K p ↔ ∀ n : ℕ, θ ((φ ^ n) a) = 0 := by sorry
