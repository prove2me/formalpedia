-- Prove2me | Theorems.Thm_GroundTheory_LocalField_inertiaQuotientToResidueUnits_injective
-- name    : GroundTheory.LocalField.inertiaQuotientToResidueUnits_injective
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:21:43.1968+00:00
-- url     : https://prove2.me/theorems/762f8f35-9bdf-47ad-8702-81df5c1b8d9b
-- title:
--   Local Field: inertia Quotient To Residue Units injective
-- statement:
--   The Local Field construction uses the inertia Quotient To Residue Units injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/RamificationStructure.lean#L47-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/RamificationStructure.lean#L47-L49

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_RamificationUnits
import Definitions.Def_GroundTheory_LocalFields_RamificationStructure
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.LocalField
open ValuativeRel IsLocalRing
variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]
variable {ϖ : 𝒪[L]} (hϖ : Irreducible ϖ)
include hϖ

theorem GroundTheory.LocalField.inertiaQuotientToResidueUnits_injective :
    Function.Injective (inertiaQuotientToResidueUnits (K := K) hϖ) := by sorry
