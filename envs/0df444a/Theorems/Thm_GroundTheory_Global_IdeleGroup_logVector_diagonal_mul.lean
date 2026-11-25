-- Prove2me | Theorems.Thm_GroundTheory_Global_IdeleGroup_logVector_diagonal_mul
-- name    : GroundTheory.Global.IdeleGroup.logVector_diagonal_mul
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T01:18:23.390668+00:00
-- url     : https://prove2.me/theorems/3d741762-ac73-49b0-8690-ba9fa28d2f1f
-- title:
--   Idele Group: log Vector diagonal mul
-- statement:
--   The Idele Group construction uses the log Vector diagonal mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/IdeleGroups/UnitBound.lean#L142-L151
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/IdeleGroups/UnitBound.lean#L142-L151

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

theorem GroundTheory.Global.IdeleGroup.logVector_diagonal_mul (u : (𝓞 K)ˣ) (y : IdeleGroup K) :
    logVector (diagonal K (unitsToUnits K u) * y) =
      logEmbedding K (Additive.ofMul u) + logVector y := by sorry
