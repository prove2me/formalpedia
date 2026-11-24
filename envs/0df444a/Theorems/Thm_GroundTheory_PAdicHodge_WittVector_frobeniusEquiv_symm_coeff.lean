-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_WittVector_frobeniusEquiv_symm_coeff
-- name    : GroundTheory.PAdicHodge.WittVector.frobeniusEquiv_symm_coeff
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T23:46:39.940795+00:00
-- url     : https://prove2.me/theorems/5b99cedc-e5d4-40fc-91b9-1b7a3b3a09d6
-- title:
--   Witt Vector: frobenius Equiv symm coeff
-- statement:
--   The Witt Vector construction uses the frobenius Equiv symm coeff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/KerFontaineThetaCompFrobeniusEquivSymmPow.lean#L178-L182
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/KerFontaineThetaCompFrobeniusEquivSymmPow.lean#L178-L182

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

theorem GroundTheory.PAdicHodge.WittVector.frobeniusEquiv_symm_coeff (x : WittVector p R) (n : ℕ) :
    ((WittVector.frobeniusEquiv p R).symm x).coeff n = (_root_.frobeniusEquiv R p).symm (x.coeff n) := by sorry
