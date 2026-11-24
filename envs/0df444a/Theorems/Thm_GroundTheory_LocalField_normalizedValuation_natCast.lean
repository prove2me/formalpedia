-- Prove2me | Theorems.Thm_GroundTheory_LocalField_normalizedValuation_natCast
-- name    : GroundTheory.LocalField.normalizedValuation_natCast
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T23:45:52.5298+00:00
-- url     : https://prove2.me/theorems/2193a101-aff9-4280-abec-c30090d66056
-- title:
--   Local Field: normalized Valuation nat Cast
-- statement:
--   The Local Field construction uses the normalized Valuation nat Cast property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/PadicLogSeries.lean#L176-L187
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/PadicLogSeries.lean#L176-L187

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_ExistsUnitFiltrationUnitsLeAndRangePowLe
import Definitions.Def_GroundTheory_LocalFields_ExamplesCharZero
import Definitions.Def_GroundTheory_LocalFields_PadicLogSeries
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.LocalField
open ValuativeRel IsLocalRing Topology Filter
open scoped WithZero
variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable (p : ℕ) [hp : Fact p.Prime] [CharP 𝓀[K] p] [CharZero K]

theorem GroundTheory.LocalField.normalizedValuation_natCast {n : ℕ} (hn : n ≠ 0) :
    normalizedValuation K (n : K) =
      WithZero.exp (-(absRamificationIndex K * padicValNat p n : ℤ)) := by sorry
