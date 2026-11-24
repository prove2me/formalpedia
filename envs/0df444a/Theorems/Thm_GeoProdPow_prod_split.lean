-- Prove2me | Theorems.Thm_GeoProdPow_prod_split
-- name    : GeoProdPow.prod_split
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T10:50:33.44895+00:00
-- url     : https://prove2.me/theorems/8e8b77d3-d607-4f50-8822-f102adf37767
-- title:
--   Geo Prod Pow: prod split
-- statement:
--   The Geo Prod Pow construction uses the prod split property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GeometricProductBound/OneSubSumLeProd.lean#L45-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GeometricProductBound/OneSubSumLeProd.lean#L45-L55

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

theorem GeoProdPow.prod_split (g0 g1 : ℝ) (h0 : 0 < g0) (h1 : 0 < g1) (r : ℕ) :
    ∏ i ∈ Ico 1 r, ((g0 ^ i - 1) * (g1 ^ i - 1)) =
      (g0 * g1) ^ (r * (r - 1) / 2) *
        ∏ i ∈ Ico 1 r, ((1 - (g0⁻¹) ^ i) * (1 - (g1⁻¹) ^ i)) := by sorry
