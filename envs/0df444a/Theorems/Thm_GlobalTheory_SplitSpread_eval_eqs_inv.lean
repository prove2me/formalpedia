-- Prove2me | Theorems.Thm_GlobalTheory_SplitSpread_eval_eqs_inv
-- name    : GlobalTheory.SplitSpread.eval_eqs_inv
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T20:21:53.605539+00:00
-- url     : https://prove2.me/theorems/e85ee789-b39b-4885-b3fd-7bbc45997918
-- title:
--   Split Spread: eval eqs inv
-- statement:
--   The Split Spread construction uses the eval eqs inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SplittingAbsenceSpreads.lean#L97-L106
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SplittingAbsenceSpreads.lean#L97-L106

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
variable {σ : Type} [Finite σ] {A : Type} [CommRing A] {D : ℕ}

theorem GlobalTheory.SplitSpread.eval_eqs_inv {k : Type} [CommRing k] (ψ : A →+* k) (z : Var σ D → k)
    (f g : MvPolynomial σ A) (b : Bool) :
    eval₂ ψ z (eqs A D f g (Sum.inr (Sum.inr b))) =
      z (Sum.inr (Sum.inr b)) *
        MvPolynomial.eval (fun i => z (Sum.inr (Sum.inl (b, i)))) (MvPolynomial.map ψ g) - 1 := by sorry
