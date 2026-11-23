-- Prove2me | Theorems.Thm_GroundTheory_LocalField_unitsEquivIntProd_fst
-- name    : GroundTheory.LocalField.unitsEquivIntProd_fst
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:00:22.261915+00:00
-- url     : https://prove2.me/theorems/03e22a6c-a555-4d73-a0e5-592bc800c697
-- title:
--   Local Field: units Equiv Int Prod fst
-- statement:
--   The Local Field construction uses the units Equiv Int Prod fst property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/UnitsBasic.lean#L248-L257
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/UnitsBasic.lean#L248-L257

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

theorem GroundTheory.LocalField.unitsEquivIntProd_fst {ϖ : 𝒪[K]} (hϖ : Irreducible ϖ) (x : Kˣ) :
    (unitsEquivIntProd hϖ x).1 = Multiplicative.ofAdd (ord (x : K)) := by sorry
