-- Prove2me | Theorems.Thm_GlobalTheory_SplitSpread_totalDegree_sum_le
-- name    : GlobalTheory.SplitSpread.totalDegree_sum_le
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T20:21:54.042805+00:00
-- url     : https://prove2.me/theorems/7257d6f5-3cb3-4e50-a18a-0a80a3cab7b9
-- title:
--   Split Spread: total Degree sum le
-- statement:
--   The Split Spread construction uses the total Degree sum le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SplittingAbsenceSpreads.lean#L44-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SplittingAbsenceSpreads.lean#L44-L47

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NoCommonZeroSpreadsConstructibleNbhdStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SplittingAbsenceSpreads
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.SplitSpread
open MvPolynomial
variable {σ : Type} [Finite σ] (A : Type) [CommRing A] (D : ℕ)
variable {A D}

theorem GlobalTheory.SplitSpread.totalDegree_sum_le {k : Type} [CommRing k] (c : Mon σ D → k) :
    (∑ m : Mon σ D, monomial m.1 (c m)).totalDegree ≤ D := by sorry
