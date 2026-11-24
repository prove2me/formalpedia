-- Prove2me | Theorems.Thm_GlobalTheory_DegreeBound_good_algebraMap
-- name    : GlobalTheory.DegreeBound.good_algebraMap
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T12:43:47.7185+00:00
-- url     : https://prove2.me/theorems/9ec8eb67-5a85-4082-9f32-b4416ef0cb03
-- title:
--   Degree Bound: good algebra Map
-- statement:
--   The Degree Bound construction uses the good algebra Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/TotalDegreeLeOfIntegralAtInfinity.lean#L35-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/TotalDegreeLeOfIntegralAtInfinity.lean#L35-L36

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

theorem GlobalTheory.DegreeBound.good_algebraMap (y : Fin D → K) (j : Fin D) (r : ℤ) : Good y j 0 (algebraMap ℤ K r) := by sorry
