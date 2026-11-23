-- Prove2me | Theorems.Thm_GlobalTheory_Published_IsHilbertClassField_unique
-- name    : GlobalTheory.Published.IsHilbertClassField.unique
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:42:59.51942+00:00
-- url     : https://prove2.me/theorems/dabe205a-1151-49bf-b946-a9add0f0115b
-- title:
--   Is Hilbert Class Field: unique
-- statement:
--   The Is Hilbert Class Field construction uses the unique property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/PublishedFoundations/ComplexMultiplicationJPremises.lean#L81-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/PublishedFoundations/ComplexMultiplicationJPremises.lean#L81-L83

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsVariableChangeEqLatticeCurve
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsBasisEmbedding
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_PublishedFoundations_ComplexMultiplicationJPremises
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open scoped nonZeroDivisors IntermediateField
open GlobalTheory GlobalTheory.Published
variable {K : Type} [Field K] [NumberField K] [Algebra K ℂ]
omit [NumberField K]

theorem GlobalTheory.Published.IsHilbertClassField.unique {H H' : IntermediateField K ℂ} (h : IsHilbertClassField H)
    (h' : IsHilbertClassField H') : H = H' := by sorry
