-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_WittVector_mem_span_teichmuller_iff
-- name    : GroundTheory.PAdicHodge.WittVector.mem_span_teichmuller_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:50:04.953002+00:00
-- url     : https://prove2.me/theorems/ed06641d-e9e7-44bd-a3b7-e23aba222122
-- title:
--   Witt Vector: mem span teichmuller iff
-- statement:
--   The Witt Vector construction uses the mem span teichmuller iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/KerFontaineThetaCompFrobeniusEquivSymmPow.lean#L49-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/KerFontaineThetaCompFrobeniusEquivSymmPow.lean#L49-L60

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

theorem GroundTheory.PAdicHodge.WittVector.mem_span_teichmuller_iff (b : R) (y : WittVector p R) :
    y ∈ Ideal.span {teichmuller p b} ↔ ∀ n, b ^ p ^ n ∣ y.coeff n := by sorry
