-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_WittVector_span_teichmuller_pow
-- name    : GroundTheory.PAdicHodge.WittVector.span_teichmuller_pow
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:51:45.732898+00:00
-- url     : https://prove2.me/theorems/b47c8312-3b87-4018-ad74-68f35704021b
-- title:
--   Witt Vector: span teichmuller pow
-- statement:
--   The Witt Vector construction uses the span teichmuller pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/KerFontaineThetaCompFrobeniusEquivSymmPow.lean#L64-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/KerFontaineThetaCompFrobeniusEquivSymmPow.lean#L64-L66

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
omit [CharP R p]

theorem GroundTheory.PAdicHodge.WittVector.span_teichmuller_pow (b : R) (N : ℕ) :
    Ideal.span {teichmuller p b} ^ N = Ideal.span {teichmuller p (b ^ N)} := by sorry
