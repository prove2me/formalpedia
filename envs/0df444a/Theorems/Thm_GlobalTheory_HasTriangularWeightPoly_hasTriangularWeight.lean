-- Prove2me | Theorems.Thm_GlobalTheory_HasTriangularWeightPoly_hasTriangularWeight
-- name    : GlobalTheory.HasTriangularWeightPoly.hasTriangularWeight
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T14:01:35.280858+00:00
-- url     : https://prove2.me/theorems/df12a327-7ec9-49c8-8490-c723ff0f1e1f
-- title:
--   Has Triangular Weight Poly: has Triangular Weight
-- statement:
--   The Has Triangular Weight Poly construction uses the has Triangular Weight property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/ExistsIsUnitEvalOfMapResidueNeZero.lean#L243-L255
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/ExistsIsUnitEvalOfMapResidueNeZero.lean#L243-L255

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

theorem GlobalTheory.HasTriangularWeightPoly.hasTriangularWeight {V : ι → Type*} [∀ s, AddCommGroup (V s)]
    [∀ s, Module K (V s)] {a : ∀ s, Fin (r s) → ℕ}
    {p : MvPolynomial (EntryIndex (fun s => Fin (r s)) (fun s => Fin (r s))) K}
    (hp : HasTriangularWeightPoly a p) (L : ∀ s, Fin (r s) → Module.Dual K (V s)) :
    HasTriangularWeight K a fun y : ∀ s, Fin (r s) → V s =>
      MvPolynomial.eval (entries fun s => Matrix.of fun i j => L s i (y s j)) p := by sorry
