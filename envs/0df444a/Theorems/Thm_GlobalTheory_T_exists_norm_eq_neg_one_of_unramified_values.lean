-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_norm_eq_neg_one_of_unramified_values
-- name    : GlobalTheory.T.exists_norm_eq_neg_one_of_unramified_values
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T07:46:34.06987+00:00
-- url     : https://prove2.me/theorems/a3d7b42c-be66-4f29-963f-6ee70fca60bd
-- title:
--   T: exists norm eq neg one of unramified values
-- statement:
--   The T construction uses the exists norm eq neg one of unramified values property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/NegOneMemNormOfValuationEqStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/NegOneMemNormOfValuationEqStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NegOneMemNormOfValuationEq
import Mathlib
import Definitions.Def_GroundTheory_LocalFields_UnramifiedNormSurj
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NegOneMemNormOfValuationEqStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.exists_norm_eq_neg_one_of_unramified_values : ∀ (F E : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] [Algebra F E] [ValuativeExtension F E] [FiniteDimensional F E], (∀ y : E, ∃ x : F, y ≤ᵥ algebraMap F E x ∧ algebraMap F E x ≤ᵥ y) → ∃ z : E, Algebra.norm F z = -1 := by sorry
