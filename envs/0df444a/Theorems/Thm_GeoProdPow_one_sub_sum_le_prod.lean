-- Prove2me | Theorems.Thm_GeoProdPow_one_sub_sum_le_prod
-- name    : GeoProdPow.one_sub_sum_le_prod
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T10:50:25.572809+00:00
-- url     : https://prove2.me/theorems/9db98243-0f65-4c96-b92f-056ab94d16a7
-- title:
--   Geo Prod Pow: one sub sum le prod
-- statement:
--   The Geo Prod Pow construction uses the one sub sum le prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GeometricProductBound/OneSubSumLeProd.lean#L8-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GeometricProductBound/OneSubSumLeProd.lean#L8-L23

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_GeometricProductPowers_GaussianProductPowerBound
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GeometricProductBound_OneSubSumLeProd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GeoProdPow
open Finset

theorem GeoProdPow.one_sub_sum_le_prod (s : Finset ℕ) (u a : ℕ → ℝ) (h0 : ∀ i ∈ s, 0 ≤ u i)
    (h1 : ∀ i ∈ s, u i ≤ 1) (ha : ∀ i ∈ s, 1 - a i ≤ u i) :
    1 - ∑ i ∈ s, a i ≤ ∏ i ∈ s, u i := by sorry
