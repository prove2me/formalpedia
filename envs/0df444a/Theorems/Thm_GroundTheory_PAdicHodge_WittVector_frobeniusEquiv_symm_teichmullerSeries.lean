-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_WittVector_frobeniusEquiv_symm_teichmullerSeries
-- name    : GroundTheory.PAdicHodge.WittVector.frobeniusEquiv_symm_teichmullerSeries
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T13:01:26.046134+00:00
-- url     : https://prove2.me/theorems/8c8af1f5-3458-4773-a62a-c66405a32c62
-- title:
--   Witt Vector: frobenius Equiv symm teichmuller Series
-- statement:
--   The Witt Vector construction uses the frobenius Equiv symm teichmuller Series property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/KerFontaineThetaCompFrobeniusEquivSymmPow.lean#L218-L223
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/KerFontaineThetaCompFrobeniusEquivSymmPow.lean#L218-L223

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

theorem GroundTheory.PAdicHodge.WittVector.frobeniusEquiv_symm_teichmullerSeries (a : ℕ → R) :
    (WittVector.frobeniusEquiv p R).symm (WittVector.teichmullerSeries a) =
      WittVector.teichmullerSeries fun n => (_root_.frobeniusEquiv R p).symm (a n) := by sorry
