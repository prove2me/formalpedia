-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_ACris_logTermZero_eq_mul_of_lt
-- name    : GroundTheory.PAdicHodge.ACris.logTermZero_eq_mul_of_lt
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T10:09:40.461543+00:00
-- url     : https://prove2.me/theorems/d1d9a1ef-692d-4065-b02a-c07c96be61df
-- title:
--   ACris: log Term Zero eq mul of lt
-- statement:
--   The ACris construction uses the log Term Zero eq mul of lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/ACrisLog.lean#L276-L297
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/ACrisLog.lean#L276-L297

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

theorem GroundTheory.PAdicHodge.ACris.logTermZero_eq_mul_of_lt {x : AInf K p} (hx : x ∈ RingHom.ker θ) {n : ℕ} (hn : n + 1 < p) :
    ∃ w : ACrisZero K p, logTermZero hx n = algebraMap (AInf K p) (ACrisZero K p) x * w := by sorry
