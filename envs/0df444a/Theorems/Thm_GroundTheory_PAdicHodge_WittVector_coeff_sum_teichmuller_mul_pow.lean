-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_WittVector_coeff_sum_teichmuller_mul_pow
-- name    : GroundTheory.PAdicHodge.WittVector.coeff_sum_teichmuller_mul_pow
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T23:45:47.295129+00:00
-- url     : https://prove2.me/theorems/a5705640-a447-482f-98c3-1ff87c83844c
-- title:
--   Witt Vector: coeff sum teichmuller mul pow
-- statement:
--   The Witt Vector construction uses the coeff sum teichmuller mul pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/KerFontaineThetaCompFrobeniusEquivSymmPow.lean#L80-L94
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/KerFontaineThetaCompFrobeniusEquivSymmPow.lean#L80-L94

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_KerTheta
import Definitions.Def_GroundTheory_PAdicHodge_TiltValuation
import Definitions.Def_GroundTheory_PAdicHodge_KerFontaineThetaCompFrobeniusEquivSymmPow
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
open WittVector
variable {p : ℕ} [hp : Fact p.Prime] {R : Type*} [CommRing R]
variable [CharP R p]

theorem GroundTheory.PAdicHodge.WittVector.coeff_sum_teichmuller_mul_pow (a : ℕ → R) (n j : ℕ) :
    (∑ i ∈ Finset.Iic n, teichmuller p (a i) * (p : WittVector p R) ^ i).coeff j =
      if j ≤ n then a j ^ p ^ j else 0 := by sorry
