-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_WittVector_frobeniusEquiv_symm_pow_teichmuller
-- name    : GroundTheory.PAdicHodge.WittVector.frobeniusEquiv_symm_pow_teichmuller
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:49:48.720138+00:00
-- url     : https://prove2.me/theorems/0046f854-7d44-4ba8-bf7f-1174ca8dad4c
-- title:
--   Witt Vector: frobenius Equiv symm pow teichmuller
-- statement:
--   The Witt Vector construction uses the frobenius Equiv symm pow teichmuller property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/KerFontaineThetaCompFrobeniusEquivSymmPow.lean#L194-L201
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/KerFontaineThetaCompFrobeniusEquivSymmPow.lean#L194-L201

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

theorem GroundTheory.PAdicHodge.WittVector.frobeniusEquiv_symm_pow_teichmuller (a : R) (n : ℕ) :
    ((WittVector.frobeniusEquiv p R).symm ^ n) (teichmuller p a) =
      teichmuller p (((_root_.frobeniusEquiv R p).symm ^ n) a) := by sorry
