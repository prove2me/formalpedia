-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_ringEquiv_symm_pow_apply_pow_apply
-- name    : GroundTheory.PAdicHodge.ringEquiv_symm_pow_apply_pow_apply
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T23:48:04.096024+00:00
-- url     : https://prove2.me/theorems/909431f1-e892-4371-962a-c47ee34f832d
-- title:
--   PAdic Hodge: ring Equiv symm pow apply pow apply
-- statement:
--   The PAdic Hodge construction uses the ring Equiv symm pow apply pow apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/KerFontaineThetaCompFrobeniusEquivSymmPow.lean#L167-L172
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/KerFontaineThetaCompFrobeniusEquivSymmPow.lean#L167-L172

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
omit [CharP R p] [PerfectRing R p]

theorem GroundTheory.PAdicHodge.ringEquiv_symm_pow_apply_pow_apply {S : Type*} [Semiring S] (f : S ≃+* S) (n : ℕ)
    (y : S) : (f.symm ^ n) ((f ^ n) y) = y := by sorry
