-- Prove2me | Theorems.Thm_GlobalTheory_finrank_int_eq_mul_of_finite
-- name    : GlobalTheory.finrank_int_eq_mul_of_finite
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:24:49.8522+00:00
-- url     : https://prove2.me/theorems/382cab94-2da7-4ce1-977b-f292ad0bec6a
-- title:
--   Global Theory: finrank int eq mul of finite
-- statement:
--   The Global Theory construction uses the finrank int eq mul of finite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/HostGeneratorPowFourTraceNormModEight.lean#L16-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/HostGeneratorPowFourTraceNormModEight.lean#L16-L65

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsIsSymplecticBasisToMatrixOffDiagDvd
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_IsCoprimeTwoSubRtTwoAddRt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_HostGeneratorPowFourTraceNormModEight
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
open NumberField Matrix
open scoped nonZeroDivisors

theorem GlobalTheory.finrank_int_eq_mul_of_finite {O M : Type*} [CommRing O] [IsDomain O] [CharZero O]
    [Module.Free ℤ O] [Module.Finite ℤ O] [AddCommGroup M] [Module O M] [Module.Finite O M] :
    Module.finrank ℤ M = Module.finrank ℤ O * Module.finrank O M := by sorry
