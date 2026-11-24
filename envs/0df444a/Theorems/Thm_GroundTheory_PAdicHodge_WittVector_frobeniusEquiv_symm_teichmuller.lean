-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_WittVector_frobeniusEquiv_symm_teichmuller
-- name    : GroundTheory.PAdicHodge.WittVector.frobeniusEquiv_symm_teichmuller
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:49:57.424793+00:00
-- url     : https://prove2.me/theorems/18122846-69cb-4769-8d4f-f17393ee1bb0
-- title:
--   Witt Vector: frobenius Equiv symm teichmuller
-- statement:
--   The Witt Vector construction uses the frobenius Equiv symm teichmuller property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/KerFontaineThetaCompFrobeniusEquivSymmPow.lean#L188-L192
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/KerFontaineThetaCompFrobeniusEquivSymmPow.lean#L188-L192

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

theorem GroundTheory.PAdicHodge.WittVector.frobeniusEquiv_symm_teichmuller (a : R) :
    (WittVector.frobeniusEquiv p R).symm (teichmuller p a) =
      teichmuller p ((_root_.frobeniusEquiv R p).symm a) := by sorry
