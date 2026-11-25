-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_ACris_dpow_p_pow_succ
-- name    : GroundTheory.PAdicHodge.ACris.dpow_p_pow_succ
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T10:13:15.686913+00:00
-- url     : https://prove2.me/theorems/302e4803-5396-49e5-aa85-2829eace94ea
-- title:
--   ACris: dpow p pow succ
-- statement:
--   The ACris construction uses the dpow p pow succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/FontaineLemmaPeriod.lean#L74-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/FontaineLemmaPeriod.lean#L74-L84

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

theorem GroundTheory.PAdicHodge.ACris.dpow_p_pow_succ (x : AInf K p) (j : ℕ) :
    dpow p x ^ (j + 1) =
      ((∏ i ∈ Finset.range j, ((i + 2) * p).choose p : ℕ) : 𝔸) * dpow ((j + 1) * p) x := by sorry
