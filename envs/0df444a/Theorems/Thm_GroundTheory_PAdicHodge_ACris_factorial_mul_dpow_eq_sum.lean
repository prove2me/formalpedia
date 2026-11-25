-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_ACris_factorial_mul_dpow_eq_sum
-- name    : GroundTheory.PAdicHodge.ACris.factorial_mul_dpow_eq_sum
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T10:18:48.322623+00:00
-- url     : https://prove2.me/theorems/bb07f0fa-3800-5ac0-9c26-0403ce80e30f
-- title:
--   ACris: factorial mul dpow eq sum
-- statement:
--   The ACris construction uses the factorial mul dpow eq sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/ACrisPhi.lean#L104-L124
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/ACrisPhi.lean#L104-L124

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

theorem GroundTheory.PAdicHodge.ACris.factorial_mul_dpow_eq_sum (x : AInf K p) (n L : ℕ) (hL : p * (n + 1) ≤ L) :
    (n.factorial : 𝔸) * dpow (n + 1) ((1 + x) ^ p - 1) =
      ∑ j ∈ Finset.range L, ((powCoeff p (n + 1) (j + 1) *
        (((j + 1).factorial / (n + 1) : ℕ) : ℤ) : ℤ) : 𝔸) * dpow (j + 1) x := by sorry
