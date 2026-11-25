-- Prove2me | Theorems.Thm_GlobalTheory_exists_prod_X_sub_C_eq
-- name    : GlobalTheory.exists_prod_X_sub_C_eq
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T02:55:26.881793+00:00
-- url     : https://prove2.me/theorems/524b86d9-e333-53b6-bf38-2d671a5bfab2
-- title:
--   Global Theory: exists prod X sub C eq
-- statement:
--   The Global Theory construction uses the exists prod X sub C eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/ExistsMeasurableRootsEnumeration.lean#L40-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/ExistsMeasurableRootsEnumeration.lean#L40-L49

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

theorem GlobalTheory.exists_prod_X_sub_C_eq {δ : ℕ} (c : Fin δ → ℂ) :
    ∃ r : Fin δ → ℂ,
      ∏ j, (X - C (r j)) = X ^ δ + ∑ i : Fin δ, C (c i) * X ^ (i : ℕ) := by sorry
