-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_ACris_dpow_p_pow_p_mem
-- name    : GroundTheory.PAdicHodge.ACris.dpow_p_pow_p_mem
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T10:15:38.238508+00:00
-- url     : https://prove2.me/theorems/c7910d8b-b11d-4ab2-8f6d-64df7dbe923c
-- title:
--   ACris: dpow p pow p mem
-- statement:
--   The ACris construction uses the dpow p pow p mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/FontaineLemmaPeriod.lean#L86-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/FontaineLemmaPeriod.lean#L86-L103

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

theorem GroundTheory.PAdicHodge.ACris.dpow_p_pow_p_mem {x : AInf K p} (hx : x ∈ RingHom.ker θ) :
    (⟨dpow p x, dpow_mem hx p⟩ : ACrisZero K p) ^ p ∈ Ideal.span {(p : ACrisZero K p)} := by sorry
