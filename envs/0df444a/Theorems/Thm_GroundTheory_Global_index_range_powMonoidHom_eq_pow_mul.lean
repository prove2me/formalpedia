-- Prove2me | Theorems.Thm_GroundTheory_Global_index_range_powMonoidHom_eq_pow_mul
-- name    : GroundTheory.Global.index_range_powMonoidHom_eq_pow_mul
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T23:41:20.707801+00:00
-- url     : https://prove2.me/theorems/3de8c050-b978-4eeb-a6ec-714bb56b8be0
-- title:
--   Global: index range pow Monoid Hom eq pow mul
-- statement:
--   The Global construction uses the index range pow Monoid Hom eq pow mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ExistenceTheorem/PowerIndex.lean#L62-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ExistenceTheorem/PowerIndex.lean#L62-L77

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

theorem GroundTheory.Global.index_range_powMonoidHom_eq_pow_mul [Group.FG G] {n : ℕ} (hn : n ≠ 0) :
    (powMonoidHom n : G →* G).range.index =
      n ^ finrank ℤ (Additive (G ⧸ CommGroup.torsion G)) *
        (powMonoidHom n : CommGroup.torsion G →* CommGroup.torsion G).range.index := by sorry
