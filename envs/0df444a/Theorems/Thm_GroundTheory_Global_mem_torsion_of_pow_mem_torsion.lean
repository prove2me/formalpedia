-- Prove2me | Theorems.Thm_GroundTheory_Global_mem_torsion_of_pow_mem_torsion
-- name    : GroundTheory.Global.mem_torsion_of_pow_mem_torsion
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T23:42:56.533808+00:00
-- url     : https://prove2.me/theorems/c3654be1-fdbf-4296-adfb-ba10300d7c1d
-- title:
--   Global: mem torsion of pow mem torsion
-- statement:
--   The Global construction uses the mem torsion of pow mem torsion property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ExistenceTheorem/PowerIndex.lean#L14-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ExistenceTheorem/PowerIndex.lean#L14-L17

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

theorem GroundTheory.Global.mem_torsion_of_pow_mem_torsion {n : ℕ} (hn : n ≠ 0) {x : G}
    (hx : x ^ n ∈ CommGroup.torsion G) : x ∈ CommGroup.torsion G := by sorry
