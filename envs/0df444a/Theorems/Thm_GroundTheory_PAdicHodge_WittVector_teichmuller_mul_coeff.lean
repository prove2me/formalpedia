-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_WittVector_teichmuller_mul_coeff
-- name    : GroundTheory.PAdicHodge.WittVector.teichmuller_mul_coeff
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T23:45:46.451706+00:00
-- url     : https://prove2.me/theorems/a19f9c27-ad35-458a-86ba-aac67edf2427
-- title:
--   Witt Vector: teichmuller mul coeff
-- statement:
--   The Witt Vector construction uses the teichmuller mul coeff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/KerFontaineThetaCompFrobeniusEquivSymmPow.lean#L34-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/KerFontaineThetaCompFrobeniusEquivSymmPow.lean#L34-L47

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

theorem GroundTheory.PAdicHodge.WittVector.teichmuller_mul_coeff (a : R) (x : WittVector p R) (n : ℕ) :
    (teichmuller p a * x).coeff n = a ^ p ^ n * x.coeff n := by sorry
