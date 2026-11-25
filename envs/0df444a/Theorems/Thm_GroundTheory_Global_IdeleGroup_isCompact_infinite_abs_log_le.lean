-- Prove2me | Theorems.Thm_GroundTheory_Global_IdeleGroup_isCompact_infinite_abs_log_le
-- name    : GroundTheory.Global.IdeleGroup.isCompact_infinite_abs_log_le
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T01:13:16.541008+00:00
-- url     : https://prove2.me/theorems/543e8cae-ff4f-48e0-a167-99815ea627f8
-- title:
--   Idele Group: is Compact infinite abs log le
-- statement:
--   The Idele Group construction uses the is Compact infinite abs log le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/IdeleGroups/UnitBound.lean#L57-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/IdeleGroups/UnitBound.lean#L57-L67

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

theorem GroundTheory.Global.IdeleGroup.isCompact_infinite_abs_log_le (M : ℝ) :
    IsCompact {y : (InfiniteAdeleRing K)ˣ |
      ∀ w : InfinitePlace K, |Real.log ‖(y : InfiniteAdeleRing K) w‖| ≤ M} := by sorry
