-- Prove2me | Theorems.Thm_GroundTheory_Global_coe_logLatticeRep
-- name    : GroundTheory.Global.coe_logLatticeRep
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T04:51:19.84245+00:00
-- url     : https://prove2.me/theorems/7e89361d-b3e3-4657-a778-bb7f037bbcfb
-- title:
--   Global: coe log Lattice Rep
-- statement:
--   The Global construction uses the coe log Lattice Rep property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/HerbrandQuotients/UnitsHerbrand.lean#L153-L156
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/HerbrandQuotients/UnitsHerbrand.lean#L153-L156

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_SUnitsExact
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_SUnitsPerm
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_SUnitsRep
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_LatticeBridge
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_UnitsHerbrand
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
open NumberField NumberField.Units NumberField.Units.dirichletUnitTheorem NumberField.InfinitePlace
  MulAction Module
open scoped TensorProduct
noncomputable section
variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
omit [NumberField K] [NumberField L]

theorem GroundTheory.Global.coe_logLatticeRep (g : L ≃ₐ[K] L) (m : logLattice L) :
    (logLatticeRep K L g m : InfinitePlace L → ℝ) =
      funPermRep ℝ (L ≃ₐ[K] L) (InfinitePlace L) g m := by sorry
