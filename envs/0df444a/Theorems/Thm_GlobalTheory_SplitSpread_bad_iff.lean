-- Prove2me | Theorems.Thm_GlobalTheory_SplitSpread_bad_iff
-- name    : GlobalTheory.SplitSpread.bad_iff
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T20:21:29.684834+00:00
-- url     : https://prove2.me/theorems/7362b0f4-4199-4dc6-9577-036fa0194e55
-- title:
--   Split Spread: bad iff
-- statement:
--   The Split Spread construction uses the bad iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SplittingAbsenceSpreads.lean#L119-L158
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SplittingAbsenceSpreads.lean#L119-L158

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
variable {σ : Type} [Finite σ] {A : Type} [CommRing A]

theorem GlobalTheory.SplitSpread.bad_iff (f g : MvPolynomial σ A) (D : ℕ) (k : Type) [Field k] (ψ : A →+* k) :
    (∃ z : Var σ D → k, ∀ j, eval₂ ψ z (eqs A D f g j) = 0) ↔ Bad f g D k ψ := by sorry
