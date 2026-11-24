-- Prove2me | Theorems.Thm_GlobalTheory_adicLevelMap_closedPoint
-- name    : GlobalTheory.adicLevelMap_closedPoint
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T22:06:01.504935+00:00
-- url     : https://prove2.me/theorems/6bf00e9a-5489-42c5-8f93-dcacd1d61e2a
-- title:
--   Global Theory: adic Level Map closed Point
-- statement:
--   The Global Theory construction uses the adic Level Map closed Point property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsUniqueFactorCompletedStalkOfMap.lean#L246-L254
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsUniqueFactorCompletedStalkOfMap.lean#L246-L254

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsUniqueFactorCompletedStalkOfMap
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry IsLocalRing
universe u
open GlobalTheory
variable {R : Type u} [CommRing R] (I : Ideal R)
variable {I}
variable [IsLocalRing R]

theorem GlobalTheory.adicLevelMap_closedPoint (hI : I ≠ ⊤) {m n : ℕ} (h : m + 1 ≤ n + 1) :
    haveI := isLocalRing_quotient_pow hI m
    haveI := isLocalRing_quotient_pow hI n
    adicLevelMap I h (closedPoint (R ⧸ I ^ (m + 1))) = closedPoint (R ⧸ I ^ (n + 1)) := by sorry
