-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_exists_eq_sum_sub_one_pow
-- name    : GroundTheory.PAdicHodge.exists_eq_sum_sub_one_pow
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T23:46:58.890798+00:00
-- url     : https://prove2.me/theorems/52919729-f735-4257-b3e8-0cfe2b1dd90e
-- title:
--   PAdic Hodge: exists eq sum sub one pow
-- statement:
--   The PAdic Hodge construction uses the exists eq sum sub one pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/FWCyclotomicNorm.lean#L41-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/FWCyclotomicNorm.lean#L41-L58

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_CyclotomicTower
import Definitions.Def_GroundTheory_PAdicHodge_TiltValuation
import Definitions.Def_GroundTheory_PAdicHodge_FWCyclotomicNorm
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
open IntermediateField Polynomial
variable {p : ℕ} [Fact p.Prime]

theorem GroundTheory.PAdicHodge.exists_eq_sum_sub_one_pow {n : ℕ} {ζ : PadicAlgCl p} (hζ : IsPrimitiveRoot ζ (p ^ n))
    {x : PadicAlgCl p} (hx : x ∈ cycl p n) :
    ∃ a : ℕ → ℚ_[p], x = ∑ i ∈ Finset.range (Nat.totient (p ^ n)),
      algebraMap ℚ_[p] (PadicAlgCl p) (a i) * (ζ - 1) ^ i := by sorry
