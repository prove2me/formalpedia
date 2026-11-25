-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_ACris_logTermZero_one_add_pow
-- name    : GroundTheory.PAdicHodge.ACris.logTermZero_one_add_pow
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T10:20:29.264615+00:00
-- url     : https://prove2.me/theorems/c8ee21df-5e10-43f1-957e-5f8ef5b4afde
-- title:
--   ACris: log Term Zero one add pow
-- statement:
--   The ACris construction uses the log Term Zero one add pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/ACrisPhi.lean#L132-L143
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/ACrisPhi.lean#L132-L143

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
local notation "θ" => fontaineTheta (normInteger K) p
local notation "𝔸" => Localization.Away (p : AInf K p)
variable {x : AInf K p}

theorem GroundTheory.PAdicHodge.ACris.logTermZero_one_add_pow (hx : x ∈ RingHom.ker θ) (n L : ℕ) (hL : p * (n + 1) ≤ L) :
    logTermZero (one_add_pow_sub_one_mem hx) n =
      ∑ j ∈ Finset.range L, (logCoeff p n j : ACrisZero K p) * dpowZero hx (j + 1) := by sorry
