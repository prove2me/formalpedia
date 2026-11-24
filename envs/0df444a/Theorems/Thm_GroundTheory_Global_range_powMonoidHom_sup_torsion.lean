-- Prove2me | Theorems.Thm_GroundTheory_Global_range_powMonoidHom_sup_torsion
-- name    : GroundTheory.Global.range_powMonoidHom_sup_torsion
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T23:42:57.940894+00:00
-- url     : https://prove2.me/theorems/e1c65ac7-3f47-4dcf-b58f-84e7e3389f58
-- title:
--   Global: range pow Monoid Hom sup torsion
-- statement:
--   The Global construction uses the range pow Monoid Hom sup torsion property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ExistenceTheorem/PowerIndex.lean#L34-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ExistenceTheorem/PowerIndex.lean#L34-L54

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

theorem GroundTheory.Global.range_powMonoidHom_sup_torsion (n : ℕ) :
    (powMonoidHom n : G →* G).range ⊔ CommGroup.torsion G =
      (powMonoidHom n : G ⧸ CommGroup.torsion G →* G ⧸ CommGroup.torsion G).range.comap
        (QuotientGroup.mk' (CommGroup.torsion G)) := by sorry
