-- Prove2me | Theorems.Thm_GroundTheory_Global_range_powMonoidHom_subgroupOf_torsion
-- name    : GroundTheory.Global.range_powMonoidHom_subgroupOf_torsion
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T23:42:47.447897+00:00
-- url     : https://prove2.me/theorems/3eed18ba-8009-4185-a68c-4693694a5d5c
-- title:
--   Global: range pow Monoid Hom subgroup Of torsion
-- statement:
--   The Global construction uses the range pow Monoid Hom subgroup Of torsion property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ExistenceTheorem/PowerIndex.lean#L19-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ExistenceTheorem/PowerIndex.lean#L19-L32

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_SUnits
import Definitions.Def_GroundTheory_GlobalFields_ExistenceTheorem_PowerIndex
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
open NumberField IsDedekindDomain Module
noncomputable section
variable {G : Type*} [CommGroup G]

theorem GroundTheory.Global.range_powMonoidHom_subgroupOf_torsion {n : ℕ} (hn : n ≠ 0) :
    (powMonoidHom n : G →* G).range.subgroupOf (CommGroup.torsion G) =
      (powMonoidHom n : CommGroup.torsion G →* CommGroup.torsion G).range := by sorry
