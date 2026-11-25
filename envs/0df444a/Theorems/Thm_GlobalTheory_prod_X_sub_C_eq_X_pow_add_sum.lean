-- Prove2me | Theorems.Thm_GlobalTheory_prod_X_sub_C_eq_X_pow_add_sum
-- name    : GlobalTheory.prod_X_sub_C_eq_X_pow_add_sum
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T02:56:31.488856+00:00
-- url     : https://prove2.me/theorems/4f51a994-54ae-4b41-b4ff-758bb70c599a
-- title:
--   Global Theory: prod X sub C eq X pow add sum
-- statement:
--   The Global Theory construction uses the prod X sub C eq X pow add sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/ExistsMeasurableRootsEnumeration.lean#L28-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/ExistsMeasurableRootsEnumeration.lean#L28-L38

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ValuationResidueLemmas
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_AlgebraMapOLInjective
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_NormOrderStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_ExistsProdXSubCOfMonic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_ExistsMeasurableRootsEnumeration
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.T0
open scoped TensorProduct
open GlobalTheory
open Polynomial

theorem GlobalTheory.prod_X_sub_C_eq_X_pow_add_sum {δ : ℕ} (r : Fin δ → ℂ) :
    ∏ j, (X - C (r j)) =
      X ^ δ + ∑ i : Fin δ, C ((∏ j, (X - C (r j))).coeff i) * X ^ (i : ℕ) := by sorry
