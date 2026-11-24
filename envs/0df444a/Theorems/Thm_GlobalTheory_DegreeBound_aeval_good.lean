-- Prove2me | Theorems.Thm_GlobalTheory_DegreeBound_aeval_good
-- name    : GlobalTheory.DegreeBound.aeval_good
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T12:43:37.856932+00:00
-- url     : https://prove2.me/theorems/d0317303-1e3d-44b6-aa60-0a910a1d69ae
-- title:
--   Degree Bound: aeval good
-- statement:
--   The Degree Bound construction uses the aeval good property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/TotalDegreeLeOfIntegralAtInfinity.lean#L38-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/TotalDegreeLeOfIntegralAtInfinity.lean#L38-L48

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TotalDegreeLeOfIntegralAtInfinity
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
open GlobalTheory GlobalTheory.DegreeBound
variable {K : Type} [Field K] {D : ℕ}

theorem GlobalTheory.DegreeBound.aeval_good {ι : Type} {y : Fin D → K} {j : Fin D} {z : ι → K}
    (hz : ∀ i, ∃ N, Good y j N (z i)) (a : MvPolynomial ι ℤ) : ∃ N, Good y j N (aeval z a) := by sorry
