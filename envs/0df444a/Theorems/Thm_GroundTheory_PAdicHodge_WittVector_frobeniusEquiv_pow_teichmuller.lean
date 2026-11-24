-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_WittVector_frobeniusEquiv_pow_teichmuller
-- name    : GroundTheory.PAdicHodge.WittVector.frobeniusEquiv_pow_teichmuller
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T10:38:37.922382+00:00
-- url     : https://prove2.me/theorems/86dcdb12-b358-421a-8789-3b83e9ae6636
-- title:
--   Witt Vector: frobenius Equiv pow teichmuller
-- statement:
--   The Witt Vector construction uses the frobenius Equiv pow teichmuller property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/KerFontaineThetaCompFrobeniusEquivSymmPow.lean#L203-L209
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/KerFontaineThetaCompFrobeniusEquivSymmPow.lean#L203-L209

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
variable {p : ℕ} [hp : Fact p.Prime] {R : Type*} [CommRing R] [CharP R p] [PerfectRing R p]

theorem GroundTheory.PAdicHodge.WittVector.frobeniusEquiv_pow_teichmuller (a : R) (n : ℕ) :
    (WittVector.frobeniusEquiv p R ^ n) (teichmuller p a) = teichmuller p (a ^ p ^ n) := by sorry
