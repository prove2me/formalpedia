-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_ACris_sum_p_mul_logTermZero_sub_mem
-- name    : GroundTheory.PAdicHodge.ACris.sum_p_mul_logTermZero_sub_mem
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T10:15:32.840587+00:00
-- url     : https://prove2.me/theorems/88e5db08-af48-48f2-b3f3-64d9f8f68e41
-- title:
--   ACris: sum p mul log Term Zero sub mem
-- statement:
--   The ACris construction uses the sum p mul log Term Zero sub mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/ACrisPhi.lean#L172-L200
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/ACrisPhi.lean#L172-L200

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_ACrisLog
import Definitions.Def_GroundTheory_PAdicHodge_LogPowSeries
import Definitions.Def_GroundTheory_PAdicHodge_ACrisPhi
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
open _root_.WittVector Polynomial
open GroundTheory.PAdicHodge.ACris
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
variable {p : ℕ} [hp : Fact p.Prime] [IsPerfectoidField K p]
local notation "𝒪♭" => PreTilt (normInteger K) p
local notation "θ" => fontaineTheta (normInteger K) p
local notation "𝔸" => Localization.Away (p : AInf K p)
local notation "φ" => WittVector.frobeniusEquiv p (PreTilt (normInteger K) p)
local notation "𝔭" => Ideal.span {(p : ACris K p)}
local notation "𝔭₀" => Ideal.span {(p : ACrisZero K p)}
variable {x : AInf K p}

theorem GroundTheory.PAdicHodge.ACris.sum_p_mul_logTermZero_sub_mem (hx : x ∈ RingHom.ker θ) {k M : ℕ} (hM : p * (p * k + 1) ≤ M) :
    ∑ j ∈ Finset.range M, (p : ACrisZero K p) * logTermZero hx j -
      ∑ n ∈ Finset.range M, logTermZero (one_add_pow_sub_one_mem hx) n ∈ 𝔭₀ ^ k := by sorry
