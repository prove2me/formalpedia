-- Prove2me | Theorems.Thm_GlobalTheory_SplitSpread_sum_coeff
-- name    : GlobalTheory.SplitSpread.sum_coeff
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T20:22:02.960737+00:00
-- url     : https://prove2.me/theorems/a7a8e779-184a-4bd3-8026-33f6518cdf2f
-- title:
--   Split Spread: sum coeff
-- statement:
--   The Split Spread construction uses the sum coeff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SplittingAbsenceSpreads.lean#L49-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SplittingAbsenceSpreads.lean#L49-L66

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

theorem GlobalTheory.SplitSpread.sum_coeff {k : Type} [CommRing k] (p : MvPolynomial σ k) (hp : p.totalDegree ≤ D) :
    ∑ m : Mon σ D, monomial m.1 (coeff m.1 p) = p := by sorry
