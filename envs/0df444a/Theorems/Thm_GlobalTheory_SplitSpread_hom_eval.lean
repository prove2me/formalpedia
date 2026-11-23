-- Prove2me | Theorems.Thm_GlobalTheory_SplitSpread_hom_eval
-- name    : GlobalTheory.SplitSpread.hom_eval
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:30:59.800804+00:00
-- url     : https://prove2.me/theorems/7dcd944f-f594-4c2b-a0d3-68bb56eabdad
-- title:
--   Split Spread: hom eval
-- statement:
--   The Split Spread construction uses the hom eval property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SplittingAbsenceSpreads.lean#L22-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SplittingAbsenceSpreads.lean#L22-L24

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

theorem GlobalTheory.SplitSpread.hom_eval {R S τ : Type} [CommSemiring R] [CommSemiring S] (h : R →+* S) (x : τ → R)
    (W : MvPolynomial τ R) : h (eval x W) = MvPolynomial.eval (h ∘ x) (MvPolynomial.map h W) := by sorry
