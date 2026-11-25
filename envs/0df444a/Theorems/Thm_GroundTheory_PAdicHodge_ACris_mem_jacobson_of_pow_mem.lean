-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_ACris_mem_jacobson_of_pow_mem
-- name    : GroundTheory.PAdicHodge.ACris.mem_jacobson_of_pow_mem
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T10:12:55.440071+00:00
-- url     : https://prove2.me/theorems/44bc2fd5-7b08-4887-a689-cfbbc0f0500a
-- title:
--   ACris: mem jacobson of pow mem
-- statement:
--   The ACris construction uses the mem jacobson of pow mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/FontaineLemmaPeriod.lean#L151-L153
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/FontaineLemmaPeriod.lean#L151-L153

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_ACrisLog
import Definitions.Def_GroundTheory_PAdicHodge_FontaineLemmaPeriod
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
open _root_.WittVector
open GroundTheory.PAdicHodge.ACris
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
variable {p : ℕ} [hp : Fact p.Prime] [IsPerfectoidField K p]
local notation "𝒪♭" => PreTilt (normInteger K) p
local notation "θ" => fontaineTheta (normInteger K) p
local notation "𝔸" => Localization.Away (p : AInf K p)
local notation "φ" => WittVector.frobeniusEquiv p (PreTilt (normInteger K) p)
local notation "𝔭" => Ideal.span {(p : ACris K p)}

theorem GroundTheory.PAdicHodge.ACris.mem_jacobson_of_pow_mem {x : ACris K p} {m : ℕ} (h : x ^ m ∈ 𝔭) :
    x ∈ (⊥ : Ideal (ACris K p)).jacobson := by sorry
