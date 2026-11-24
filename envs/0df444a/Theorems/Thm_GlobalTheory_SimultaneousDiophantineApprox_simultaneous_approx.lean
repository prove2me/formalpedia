-- Prove2me | Theorems.Thm_GlobalTheory_SimultaneousDiophantineApprox_simultaneous_approx
-- name    : GlobalTheory.SimultaneousDiophantineApprox.simultaneous_approx
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T20:12:19.300868+00:00
-- url     : https://prove2.me/theorems/93eb1fd1-605b-497a-8f2d-253f216abc14
-- title:
--   Simultaneous Diophantine Approx: simultaneous approx
-- statement:
--   The Simultaneous Diophantine Approx construction uses the simultaneous approx property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/ExistsBoundedMultipleNearInteger.lean#L7-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/ExistsBoundedMultipleNearInteger.lean#L7-L55

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsBoundedMultipleNearInteger
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.SimultaneousDiophantineApprox
open NumberField

theorem GlobalTheory.SimultaneousDiophantineApprox.simultaneous_approx {ι : Type} [Fintype ι] (N : ℕ) (hN : 0 < N) (a : ι → ℚ) :
    ∃ m : ℕ, 0 < m ∧ m ≤ N ^ Fintype.card ι ∧ ∃ z : ι → ℤ,
      ∀ i, |(m : ℚ) * a i - z i| ≤ 1 / N := by sorry
