-- Prove2me | Theorems.Thm_GlobalTheory_HermModel_finrank_eq_of_injective_of_span
-- name    : GlobalTheory.HermModel.finrank_eq_of_injective_of_span
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:40:31.96781+00:00
-- url     : https://prove2.me/theorems/b9565625-9a28-4663-80e6-c6f5642036fe
-- title:
--   Herm Model: finrank eq of injective of span
-- statement:
--   The Herm Model construction uses the finrank eq of injective of span property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/FinrankEqOfInjectiveOfSpan.lean#L14-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/FinrankEqOfInjectiveOfSpan.lean#L14-L38

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_FinrankEqOfInjectiveOfSpan
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
open GlobalTheory GlobalTheory.HermModel
open NumberField Matrix
open scoped nonZeroDivisors

theorem GlobalTheory.HermModel.finrank_eq_of_injective_of_span {R K M V : Type} [CommRing R] [IsDomain R]
    [Field K] [Algebra R K] [IsFractionRing R K] [AddCommGroup M] [Module R M] [AddCommGroup V]
    [Module R V] [Module K V] [IsScalarTower R K V] (f : M →ₗ[R] V) (hf : Function.Injective f)
    (hspan : Submodule.span K (Set.range f) = ⊤) :
    Module.finrank R M = Module.finrank K V := by sorry
