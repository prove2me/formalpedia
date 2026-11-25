-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_ACris_one_add_pow_sub_one_pow_eq_sum
-- name    : GroundTheory.PAdicHodge.ACris.one_add_pow_sub_one_pow_eq_sum
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T10:16:48.156017+00:00
-- url     : https://prove2.me/theorems/ecdabcbe-b5a2-496e-99f3-0897cc90d04b
-- title:
--   ACris: one add pow sub one pow eq sum
-- statement:
--   The ACris construction uses the one add pow sub one pow eq sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/ACrisPhi.lean#L93-L102
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/ACrisPhi.lean#L93-L102

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

theorem GroundTheory.PAdicHodge.ACris.one_add_pow_sub_one_pow_eq_sum (x : AInf K p) (N L : ℕ) (hL : p * N ≤ L) :
    ((1 + x) ^ p - 1) ^ N =
      ∑ m ∈ Finset.range (L + 1), (powCoeff p N m : AInf K p) * x ^ m := by sorry
