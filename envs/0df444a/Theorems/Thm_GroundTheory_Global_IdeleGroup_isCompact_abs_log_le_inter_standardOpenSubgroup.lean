-- Prove2me | Theorems.Thm_GroundTheory_Global_IdeleGroup_isCompact_abs_log_le_inter_standardOpenSubgroup
-- name    : GroundTheory.Global.IdeleGroup.isCompact_abs_log_le_inter_standardOpenSubgroup
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T01:13:14.86011+00:00
-- url     : https://prove2.me/theorems/feb20ff1-236f-4004-98df-b619dbdf369b
-- title:
--   Idele Group: is Compact abs log le inter standard Open Subgroup
-- statement:
--   The Idele Group construction uses the is Compact abs log le inter standard Open Subgroup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/IdeleGroups/UnitBound.lean#L83-L99
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/IdeleGroups/UnitBound.lean#L83-L99

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

theorem GroundTheory.Global.IdeleGroup.isCompact_abs_log_le_inter_standardOpenSubgroup (M : ℝ) :
    IsCompact {x : IdeleGroup K | (∀ w : InfinitePlace K, |Real.log ‖(x : 𝔸[K]).1 w‖| ≤ M) ∧
      x ∈ standardOpenSubgroup K} := by sorry
