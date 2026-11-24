-- Prove2me | Theorems.Thm_GeoProdPow_geom_le
-- name    : GeoProdPow.geom_le
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T10:50:23.79311+00:00
-- url     : https://prove2.me/theorems/66669e56-55b4-484a-9cb2-5e68f2b60175
-- title:
--   Geo Prod Pow: geom le
-- statement:
--   The Geo Prod Pow construction uses the geom le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GeometricProductBound/OneSubSumLeProd.lean#L25-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GeometricProductBound/OneSubSumLeProd.lean#L25-L33

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

theorem GeoProdPow.geom_le (g : ℝ) (hg : 1 < g) (r : ℕ) :
    ∑ i ∈ Ico 1 r, (g⁻¹) ^ i ≤ 1 / (g - 1) := by sorry
