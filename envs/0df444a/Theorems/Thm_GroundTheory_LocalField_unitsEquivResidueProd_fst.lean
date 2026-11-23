-- Prove2me | Theorems.Thm_GroundTheory_LocalField_unitsEquivResidueProd_fst
-- name    : GroundTheory.LocalField.unitsEquivResidueProd_fst
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:28:37.848801+00:00
-- url     : https://prove2.me/theorems/180b4ddd-7eaf-4561-8937-77847ead6cc0
-- title:
--   Local Field: units Equiv Residue Prod fst
-- statement:
--   The Local Field construction uses the units Equiv Residue Prod fst property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/UnitsPowers.lean#L145-L146
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/UnitsPowers.lean#L145-L146

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_UnitsBasic
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ExistsRootOfAdicComplete
import Definitions.Def_GroundTheory_LocalFields_UnitsPowers
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
open ValuativeRel IsLocalRing Polynomial
open scoped WithZero
variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable {K}
variable (K)
variable {K}
variable (K)
variable {K}
variable (K)

theorem GroundTheory.LocalField.unitsEquivResidueProd_fst (u : 𝒪[K]ˣ) :
    (unitsEquivResidueProd K u).1 = unitsToResidue K u := by sorry

attribute [defeq] GroundTheory.LocalField.unitsEquivResidueProd_fst
