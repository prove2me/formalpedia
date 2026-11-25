-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_ACris_xi_sub_pow_mem
-- name    : GroundTheory.PAdicHodge.ACris.xi_sub_pow_mem
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T10:07:48.993582+00:00
-- url     : https://prove2.me/theorems/7109101c-22d5-5bea-911c-c057d5cbec07
-- title:
--   ACris: xi sub pow mem
-- statement:
--   The ACris construction uses the xi sub pow mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/ACrisLog.lean#L235-L251
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/ACrisLog.lean#L235-L251

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_FactorizationFactorialLe
import Definitions.Def_GroundTheory_PAdicHodge_ACrisLog
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
local notation "𝒪♭" => PreTilt (normInteger K) p
local notation "θ" => fontaineTheta (normInteger K) p
local notation "𝔸" => Localization.Away (p : AInf K p)
local notation "φ" => WittVector.frobeniusEquiv p (PreTilt (normInteger K) p)
local notation "𝔭" => Ideal.span {(p : ACris K p)}

theorem GroundTheory.PAdicHodge.ACris.xi_sub_pow_mem (ε : 𝒪♭) :
    AInf.xi (K := K) ε - ((φ).symm (AInf.mu ε)) ^ (p - 1) ∈ Ideal.span {(p : AInf K p)} := by sorry
