-- Prove2me | Theorems.Thm_GlobalTheory_eval_detProdPoly
-- name    : GlobalTheory.eval_detProdPoly
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T10:43:35.649113+00:00
-- url     : https://prove2.me/theorems/40d273d5-4b6d-45a2-a346-18c094461ed4
-- title:
--   Global Theory: eval det Prod Poly
-- statement:
--   The Global Theory construction uses the eval det Prod Poly property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/ExistsIsUnitEvalOfMapResidueNeZero.lean#L271-L274
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/ExistsIsUnitEvalOfMapResidueNeZero.lean#L271-L274

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

theorem GlobalTheory.eval_detProdPoly {R : Type*} [CommRing R] {n : ι → Type*}
    [∀ s, Fintype (n s)] [∀ s, DecidableEq (n s)] (ξ : EntryIndex n n → R) :
    MvPolynomial.eval ξ (detProdPoly R n) = ∏ s, (ofEntries ξ s).det := by sorry
