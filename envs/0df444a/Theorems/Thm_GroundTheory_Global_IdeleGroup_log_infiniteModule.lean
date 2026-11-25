-- Prove2me | Theorems.Thm_GroundTheory_Global_IdeleGroup_log_infiniteModule
-- name    : GroundTheory.Global.IdeleGroup.log_infiniteModule
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T01:18:22.365312+00:00
-- url     : https://prove2.me/theorems/60844a04-d9d3-42ad-8bf5-01dc39380826
-- title:
--   Idele Group: log infinite Module
-- statement:
--   The Idele Group construction uses the log infinite Module property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/IdeleGroups/UnitBound.lean#L132-L137
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/IdeleGroups/UnitBound.lean#L132-L137

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_IdeleNorms
import Definitions.Def_GroundTheory_GlobalFields_Adele_Compact
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_UnitBound
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
open NumberField IsDedekindDomain Topology Filter NumberField.Units
  NumberField.Units.dirichletUnitTheorem
open scoped NumberField.AdeleRing RestrictedProduct
noncomputable section
variable (K : Type*) [Field K] [NumberField K]
open GroundTheory.Global.IdeleGroup
variable {K}

theorem GroundTheory.Global.IdeleGroup.log_infiniteModule (x : IdeleGroup K) :
    Real.log (infiniteModule x) =
      ∑ w : InfinitePlace K, (w.mult : ℝ) * Real.log ‖(x : 𝔸[K]).1 w‖ := by sorry
