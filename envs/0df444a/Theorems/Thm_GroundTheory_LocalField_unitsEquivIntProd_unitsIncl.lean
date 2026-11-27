-- Prove2me | Theorems.Thm_GroundTheory_LocalField_unitsEquivIntProd_unitsIncl
-- name    : GroundTheory.LocalField.unitsEquivIntProd_unitsIncl
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T13:00:47.689903+00:00
-- url     : https://prove2.me/theorems/a2c80495-9217-58d5-8432-0f2927b5b0e5
-- title:
--   Local Field: units Equiv Int Prod units Incl
-- statement:
--   The Local Field construction uses the units Equiv Int Prod units Incl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/UnitsBasic.lean#L265-L269
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/UnitsBasic.lean#L265-L269

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_UnitsBasic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.LocalField
open ValuativeRel IsLocalRing
open scoped WithZero
variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable {K}

theorem GroundTheory.LocalField.unitsEquivIntProd_unitsIncl {ϖ : 𝒪[K]} (hϖ : Irreducible ϖ) (u : 𝒪[K]ˣ) :
    unitsEquivIntProd hϖ (unitsIncl K u) = (1, u) := by sorry
