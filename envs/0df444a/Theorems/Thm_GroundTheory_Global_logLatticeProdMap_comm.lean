-- Prove2me | Theorems.Thm_GroundTheory_Global_logLatticeProdMap_comm
-- name    : GroundTheory.Global.logLatticeProdMap_comm
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T06:15:48.72133+00:00
-- url     : https://prove2.me/theorems/ffef8a9e-7f17-44c4-90da-64eb89a3ae0f
-- title:
--   Global: log Lattice Prod Map comm
-- statement:
--   The Global construction uses the log Lattice Prod Map comm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/HerbrandQuotients/UnitsHerbrandValue.lean#L33-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/HerbrandQuotients/UnitsHerbrandValue.lean#L33-L39

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
omit [NumberField K] [NumberField L]

theorem GroundTheory.Global.logLatticeProdMap_comm (g : L ≃ₐ[K] L) (x : logLattice L × ℤ) :
    logLatticeProdMap (((logLatticeRep K L).prod (Representation.trivial ℤ (L ≃ₐ[K] L) ℤ)) g x) =
      funPermRep ℝ (L ≃ₐ[K] L) (InfinitePlace L) g (logLatticeProdMap x) := by sorry
