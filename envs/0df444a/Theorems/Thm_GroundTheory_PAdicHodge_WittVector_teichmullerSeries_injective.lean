-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_WittVector_teichmullerSeries_injective
-- name    : GroundTheory.PAdicHodge.WittVector.teichmullerSeries_injective
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T13:01:19.370107+00:00
-- url     : https://prove2.me/theorems/6c592697-173d-5725-b60d-76c63cda756d
-- title:
--   Witt Vector: teichmuller Series injective
-- statement:
--   The Witt Vector construction uses the teichmuller Series injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/KerFontaineThetaCompFrobeniusEquivSymmPow.lean#L148-L154
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/KerFontaineThetaCompFrobeniusEquivSymmPow.lean#L148-L154

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

theorem GroundTheory.PAdicHodge.WittVector.teichmullerSeries_injective :
    Function.Injective (WittVector.teichmullerSeries (p := p) (R := R)) := by sorry
