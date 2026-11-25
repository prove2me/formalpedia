-- Prove2me | Theorems.Thm_GroundTheory_LocalField_unitsEquivIntProd_uniformizer
-- name    : GroundTheory.LocalField.unitsEquivIntProd_uniformizer
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T13:00:41.767012+00:00
-- url     : https://prove2.me/theorems/413bfefa-4e88-465d-b8ac-dda4f459da56
-- title:
--   Local Field: units Equiv Int Prod uniformizer
-- statement:
--   The Local Field construction uses the units Equiv Int Prod uniformizer property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/UnitsBasic.lean#L259-L263
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/UnitsBasic.lean#L259-L263

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

theorem GroundTheory.LocalField.unitsEquivIntProd_uniformizer {ϖ : 𝒪[K]} (hϖ : Irreducible ϖ) :
    unitsEquivIntProd hϖ (uniformizerUnit hϖ) = (Multiplicative.ofAdd 1, 1) := by sorry
