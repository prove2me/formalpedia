-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_WittVector_dvd_sub_sum_teichmullerSeries
-- name    : GroundTheory.PAdicHodge.WittVector.dvd_sub_sum_teichmullerSeries
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:49:32.509903+00:00
-- url     : https://prove2.me/theorems/bed3d44f-f1d7-4beb-8eca-05b246e8fba3
-- title:
--   Witt Vector: dvd sub sum teichmuller Series
-- statement:
--   The Witt Vector construction uses the dvd sub sum teichmuller Series property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/KerFontaineThetaCompFrobeniusEquivSymmPow.lean#L115-L118
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/KerFontaineThetaCompFrobeniusEquivSymmPow.lean#L115-L118

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
variable [PerfectRing R p]

theorem GroundTheory.PAdicHodge.WittVector.dvd_sub_sum_teichmullerSeries (a : ℕ → R) (n : ℕ) :
    (p : WittVector p R) ^ (n + 1) ∣ WittVector.teichmullerSeries a -
      ∑ i ∈ Finset.Iic n, teichmuller p (a i) * (p : WittVector p R) ^ i := by sorry
