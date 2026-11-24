-- Prove2me | Theorems.Thm_GeoProdPow_factor
-- name    : GeoProdPow.factor
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T10:50:30.257463+00:00
-- url     : https://prove2.me/theorems/311aedb7-7b6a-4abf-a287-2a8283e2d5e8
-- title:
--   Geo Prod Pow: factor
-- statement:
--   The Geo Prod Pow construction uses the factor property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GeometricProductBound/OneSubSumLeProd.lean#L35-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GeometricProductBound/OneSubSumLeProd.lean#L35-L36

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

theorem GeoProdPow.factor (g : ℝ) (hg : 0 < g) (i : ℕ) : g ^ i - 1 = g ^ i * (1 - (g⁻¹) ^ i) := by sorry
