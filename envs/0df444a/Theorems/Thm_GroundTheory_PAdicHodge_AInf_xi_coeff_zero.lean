-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_AInf_xi_coeff_zero
-- name    : GroundTheory.PAdicHodge.AInf.xi_coeff_zero
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T23:46:05.65979+00:00
-- url     : https://prove2.me/theorems/1c476ce5-f334-4554-b2a6-0a27721d625d
-- title:
--   AInf: xi coeff zero
-- statement:
--   The AInf construction uses the xi coeff zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/AInfXi.lean#L188-L194
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/AInfXi.lean#L188-L194

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

theorem GroundTheory.PAdicHodge.AInf.xi_coeff_zero (ε : 𝒪♭) :
    (xi ε).coeff 0 = ∑ i ∈ Finset.range p, (_root_.frobeniusEquiv 𝒪♭ p).symm ε ^ i := by sorry
