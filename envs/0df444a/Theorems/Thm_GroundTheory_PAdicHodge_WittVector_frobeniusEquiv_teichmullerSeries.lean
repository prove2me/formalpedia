-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_WittVector_frobeniusEquiv_teichmullerSeries
-- name    : GroundTheory.PAdicHodge.WittVector.frobeniusEquiv_teichmullerSeries
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T23:45:49.088993+00:00
-- url     : https://prove2.me/theorems/c27a968a-bbbc-4bac-ae15-d6e15183a8c2
-- title:
--   Witt Vector: frobenius Equiv teichmuller Series
-- statement:
--   The Witt Vector construction uses the frobenius Equiv teichmuller Series property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/KerFontaineThetaCompFrobeniusEquivSymmPow.lean#L211-L216
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/KerFontaineThetaCompFrobeniusEquivSymmPow.lean#L211-L216

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

theorem GroundTheory.PAdicHodge.WittVector.frobeniusEquiv_teichmullerSeries (a : ℕ → R) :
    WittVector.frobeniusEquiv p R (WittVector.teichmullerSeries a) =
      WittVector.teichmullerSeries fun n => a n ^ p := by sorry
