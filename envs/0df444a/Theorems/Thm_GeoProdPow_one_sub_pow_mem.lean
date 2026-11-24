-- Prove2me | Theorems.Thm_GeoProdPow_one_sub_pow_mem
-- name    : GeoProdPow.one_sub_pow_mem
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T10:50:21.148386+00:00
-- url     : https://prove2.me/theorems/e16f519a-f8a9-4ed3-b681-4c510e7d8465
-- title:
--   Geo Prod Pow: one sub pow mem
-- statement:
--   The Geo Prod Pow construction uses the one sub pow mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GeometricProductBound/OneSubSumLeProd.lean#L57-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GeometricProductBound/OneSubSumLeProd.lean#L57-L59

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

theorem GeoProdPow.one_sub_pow_mem (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1) (i : ℕ) :
    0 ≤ 1 - x ^ i ∧ 1 - x ^ i ≤ 1 := by sorry
