-- Prove2me | Theorems.Thm_GroundTheory_LocalField_unitsEquivResidueProd_symm_apply
-- name    : GroundTheory.LocalField.unitsEquivResidueProd_symm_apply
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T07:28:34.866094+00:00
-- url     : https://prove2.me/theorems/3567575b-d7a3-4992-8db9-e268b16a4617
-- title:
--   Local Field: units Equiv Residue Prod symm apply
-- statement:
--   The Local Field construction uses the units Equiv Residue Prod symm apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/UnitsPowers.lean#L149-L150
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/UnitsPowers.lean#L149-L150

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

theorem GroundTheory.LocalField.unitsEquivResidueProd_symm_apply (ζ : 𝓀[K]ˣ) (v : unitFiltration K 1) :
    (unitsEquivResidueProd K).symm (ζ, v) = teichmuller K ζ * v := by sorry

attribute [defeq] GroundTheory.LocalField.unitsEquivResidueProd_symm_apply
