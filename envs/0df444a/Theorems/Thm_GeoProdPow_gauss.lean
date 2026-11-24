-- Prove2me | Theorems.Thm_GeoProdPow_gauss
-- name    : GeoProdPow.gauss
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T10:50:15.078059+00:00
-- url     : https://prove2.me/theorems/53950b26-c386-4048-8783-1162a0fb3490
-- title:
--   Geo Prod Pow: gauss
-- statement:
--   The Geo Prod Pow construction uses the gauss property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GeometricProductBound/OneSubSumLeProd.lean#L38-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GeometricProductBound/OneSubSumLeProd.lean#L38-L43

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

theorem GeoProdPow.gauss (r : ℕ) : ∑ i ∈ Ico 1 r, i = r * (r - 1) / 2 := by sorry
