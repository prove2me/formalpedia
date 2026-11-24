-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_frobeniusEquiv_pow_apply
-- name    : GroundTheory.PAdicHodge.frobeniusEquiv_pow_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:52:42.69273+00:00
-- url     : https://prove2.me/theorems/cb3c7774-d29b-47ec-b312-6f7a65a0de20
-- title:
--   PAdic Hodge: frobenius Equiv pow apply
-- statement:
--   The PAdic Hodge construction uses the frobenius Equiv pow apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/KerFontaineThetaCompFrobeniusEquivSymmPow.lean#L120-L126
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/KerFontaineThetaCompFrobeniusEquivSymmPow.lean#L120-L126

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

theorem GroundTheory.PAdicHodge.frobeniusEquiv_pow_apply (y : R) (n : ℕ) :
    ((_root_.frobeniusEquiv R p) ^ n) y = y ^ p ^ n := by sorry
