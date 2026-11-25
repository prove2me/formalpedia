-- Prove2me | Theorems.Thm_GroundTheory_Global_finrank_logLattice
-- name    : GroundTheory.Global.finrank_logLattice
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T04:51:33.695961+00:00
-- url     : https://prove2.me/theorems/aae10e41-0108-4486-9a60-e800eb2adc83
-- title:
--   Global: finrank log Lattice
-- statement:
--   The Global construction uses the finrank log Lattice property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/HerbrandQuotients/UnitsHerbrand.lean#L92-L93
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/HerbrandQuotients/UnitsHerbrand.lean#L92-L93

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
open scoped Classical
variable (L : Type*) [Field L] [NumberField L]

theorem GroundTheory.Global.finrank_logLattice : finrank ℤ (logLattice L) = rank L := by sorry
