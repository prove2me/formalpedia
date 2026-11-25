-- Prove2me | Theorems.Thm_GroundTheory_Global_IdeleGroup_isCompact_units_abs_log_le
-- name    : GroundTheory.Global.IdeleGroup.isCompact_units_abs_log_le
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T01:13:03.047955+00:00
-- url     : https://prove2.me/theorems/020ee3f3-552b-4bca-8a48-e559beb259de
-- title:
--   Idele Group: is Compact units abs log le
-- statement:
--   The Idele Group construction uses the is Compact units abs log le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/IdeleGroups/UnitBound.lean#L35-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/IdeleGroups/UnitBound.lean#L35-L53

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
omit [NumberField K]

theorem GroundTheory.Global.IdeleGroup.isCompact_units_abs_log_le (w : InfinitePlace K) (M : ℝ) :
    IsCompact {z : (w.Completion)ˣ | |Real.log ‖(z : w.Completion)‖| ≤ M} := by sorry
