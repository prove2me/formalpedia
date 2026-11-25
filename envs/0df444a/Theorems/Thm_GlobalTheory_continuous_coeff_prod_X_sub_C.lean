-- Prove2me | Theorems.Thm_GlobalTheory_continuous_coeff_prod_X_sub_C
-- name    : GlobalTheory.continuous_coeff_prod_X_sub_C
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T02:53:24.582796+00:00
-- url     : https://prove2.me/theorems/5d61f71a-8aa5-59ea-b850-a92c57c78a49
-- title:
--   Global Theory: continuous coeff prod X sub C
-- statement:
--   The Global Theory construction uses the continuous coeff prod X sub C property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/ExistsMeasurableRootsEnumeration.lean#L14-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/ExistsMeasurableRootsEnumeration.lean#L14-L26

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

theorem GlobalTheory.continuous_coeff_prod_X_sub_C {ι : Type} (s : Finset ι) (n : ℕ) :
    Continuous fun r : ι → ℂ => (∏ j ∈ s, (X - C (r j))).coeff n := by sorry
