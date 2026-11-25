-- Prove2me | Theorems.Thm_GlobalTheory_HasTriangularWeight_poly
-- name    : GlobalTheory.HasTriangularWeight.poly
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T12:07:22.711807+00:00
-- url     : https://prove2.me/theorems/e2cf1179-d6ae-43d4-92bf-0721ce7330c9
-- title:
--   Has Triangular Weight: poly
-- statement:
--   The Has Triangular Weight construction uses the poly property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/ExistsIsUnitEvalOfMapResidueNeZero.lean#L234-L241
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/ExistsIsUnitEvalOfMapResidueNeZero.lean#L234-L241

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsIsUnitEvalOfMapResidueNeZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped BigOperators
open Module
open GlobalTheory
variable {ι : Type*} [Fintype ι] {r : ι → ℕ} {K : Type*} [Field K]

theorem GlobalTheory.HasTriangularWeight.poly {V : ι → Type*} [∀ s, AddCommGroup (V s)] [∀ s, Module K (V s)]
    {a : ∀ s, Fin (r s) → ℕ} {P : (∀ s, Fin (r s) → V s) → K} (hP : HasTriangularWeight K a P)
    (w : ∀ s, Fin (r s) → V s)
    {p : MvPolynomial (EntryIndex (fun s => Fin (r s)) (fun s => Fin (r s))) K}
    (hp : ∀ ξ : ∀ s, Matrix (Fin (r s)) (Fin (r s)) K,
      P (frameMul w ξ) = MvPolynomial.eval (entries ξ) p) : HasTriangularWeightPoly a p := by sorry
