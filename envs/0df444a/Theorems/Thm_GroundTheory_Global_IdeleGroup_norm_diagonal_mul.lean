-- Prove2me | Theorems.Thm_GroundTheory_Global_IdeleGroup_norm_diagonal_mul
-- name    : GroundTheory.Global.IdeleGroup.norm_diagonal_mul
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T01:13:22.715065+00:00
-- url     : https://prove2.me/theorems/c79295d6-7ee4-41ab-8512-2a4a2b4e30aa
-- title:
--   Idele Group: norm diagonal mul
-- statement:
--   The Idele Group construction uses the norm diagonal mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/IdeleGroups/UnitBound.lean#L126-L130
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/IdeleGroups/UnitBound.lean#L126-L130

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

theorem GroundTheory.Global.IdeleGroup.norm_diagonal_mul (k : Kˣ) (y : IdeleGroup K) (w : InfinitePlace K) :
    ‖((diagonal K k * y : IdeleGroup K) : 𝔸[K]).1 w‖ = w (k : K) * ‖(y : 𝔸[K]).1 w‖ := by sorry
