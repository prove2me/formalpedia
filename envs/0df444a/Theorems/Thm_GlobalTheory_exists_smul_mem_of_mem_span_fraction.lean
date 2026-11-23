-- Prove2me | Theorems.Thm_GlobalTheory_exists_smul_mem_of_mem_span_fraction
-- name    : GlobalTheory.exists_smul_mem_of_mem_span_fraction
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:43:56.77071+00:00
-- url     : https://prove2.me/theorems/aa43006a-4770-45fc-8cf6-ff74c98d6c8a
-- title:
--   Global Theory: exists smul mem of mem span fraction
-- statement:
--   The Global Theory construction uses the exists smul mem of mem span fraction property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExistsSmulMemOfMemSpanFraction.lean#L16-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExistsSmulMemOfMemSpanFraction.lean#L16-L26

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_Imports
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsSmulMemOfMemSpanFraction
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix
open scoped nonZeroDivisors
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory
variable {R K : Type} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K]

theorem GlobalTheory.exists_smul_mem_of_mem_span_fraction {V : Type} [AddCommGroup V] [Module K V] [Module R V]
    [IsScalarTower R K V] (Λ : Submodule R V) (v : V) (hv : v ∈ Submodule.span K (Λ : Set V)) :
    ∃ d : R, d ≠ 0 ∧ d • v ∈ Λ := by sorry
