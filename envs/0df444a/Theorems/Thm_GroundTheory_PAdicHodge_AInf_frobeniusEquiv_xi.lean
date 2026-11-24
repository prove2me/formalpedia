-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_AInf_frobeniusEquiv_xi
-- name    : GroundTheory.PAdicHodge.AInf.frobeniusEquiv_xi
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T10:38:39.961772+00:00
-- url     : https://prove2.me/theorems/89cc4270-604f-4d8c-9a00-b51a637742c7
-- title:
--   AInf: frobenius Equiv xi
-- statement:
--   The AInf construction uses the frobenius Equiv xi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/AInfXi.lean#L82-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/AInfXi.lean#L82-L85

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

theorem GroundTheory.PAdicHodge.AInf.frobeniusEquiv_xi (ε : 𝒪♭) :
    φ (xi ε) = ∑ i ∈ Finset.range p, teichmuller p ε ^ i := by sorry
