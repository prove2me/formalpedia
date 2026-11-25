-- Prove2me | Theorems.Thm_GroundTheory_Global_logLatticeProdMap_apply
-- name    : GroundTheory.Global.logLatticeProdMap_apply
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T06:09:28.531469+00:00
-- url     : https://prove2.me/theorems/4cff6850-a18b-5d31-8963-ded19925bdb2
-- title:
--   Global: log Lattice Prod Map apply
-- statement:
--   The Global construction uses the log Lattice Prod Map apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/HerbrandQuotients/UnitsHerbrandValue.lean#L28-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/HerbrandQuotients/UnitsHerbrandValue.lean#L28-L30

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_UnitsHerbrand
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_UnitsHerbrandValue
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Global
open NumberField NumberField.Units NumberField.InfinitePlace MulAction Module
open scoped TensorProduct
noncomputable section
variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
omit [NumberField L]

theorem GroundTheory.Global.logLatticeProdMap_apply (m : logLattice L) (n : ℤ) :
    logLatticeProdMap (m, n) = (m : InfinitePlace L → ℝ) + n • (1 : InfinitePlace L → ℝ) := by sorry
