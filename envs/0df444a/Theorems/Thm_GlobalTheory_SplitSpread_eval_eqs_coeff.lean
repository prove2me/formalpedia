-- Prove2me | Theorems.Thm_GlobalTheory_SplitSpread_eval_eqs_coeff
-- name    : GlobalTheory.SplitSpread.eval_eqs_coeff
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T20:21:28.968894+00:00
-- url     : https://prove2.me/theorems/ce144290-20d1-4a2a-9871-39746d260a16
-- title:
--   Split Spread: eval eqs coeff
-- statement:
--   The Split Spread construction uses the eval eqs coeff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SplittingAbsenceSpreads.lean#L77-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SplittingAbsenceSpreads.lean#L77-L84

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

theorem GlobalTheory.SplitSpread.eval_eqs_coeff {k : Type} [CommRing k] (ψ : A →+* k) (z : Var σ D → k)
    (f g : MvPolynomial σ A) (n : σ →₀ ℕ) :
    eval₂ ψ z (eqs A D f g (Sum.inl n)) = coeff n (spec z true * spec z false - MvPolynomial.map ψ f) := by sorry
