-- Prove2me | Theorems.Thm_GlobalTheory_SplitSpread_sum_eq_degree
-- name    : GlobalTheory.SplitSpread.sum_eq_degree
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T20:22:08.086866+00:00
-- url     : https://prove2.me/theorems/80f43353-6dbd-4b91-91ae-44d398a39622
-- title:
--   Split Spread: sum eq degree
-- statement:
--   The Split Spread construction uses the sum eq degree property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SplittingAbsenceSpreads.lean#L20-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SplittingAbsenceSpreads.lean#L20-L20

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

theorem GlobalTheory.SplitSpread.sum_eq_degree {σ : Type} (s : σ →₀ ℕ) : (s.sum fun _ e => e) = s.degree := by sorry
