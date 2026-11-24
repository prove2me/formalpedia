-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_WittVector_teichmullerSeries_coeff_eq
-- name    : GroundTheory.PAdicHodge.WittVector.teichmullerSeries_coeff_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:49:37.676434+00:00
-- url     : https://prove2.me/theorems/8c17c735-363a-42a5-885a-99acff2bfa74
-- title:
--   Witt Vector: teichmuller Series coeff eq
-- statement:
--   The Witt Vector construction uses the teichmuller Series coeff eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/KerFontaineThetaCompFrobeniusEquivSymmPow.lean#L136-L140
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/KerFontaineThetaCompFrobeniusEquivSymmPow.lean#L136-L140

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

theorem GroundTheory.PAdicHodge.WittVector.teichmullerSeries_coeff_eq (x : WittVector p R) :
    WittVector.teichmullerSeries (fun n => ((_root_.frobeniusEquiv R p).symm ^ n) (x.coeff n)) =
      x := by sorry
