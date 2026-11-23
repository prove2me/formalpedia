-- Prove2me | Theorems.Thm_GlobalTheory_PeriodDatum_two_mul_eq_of_isTypeFn
-- name    : GlobalTheory.PeriodDatum.two_mul_eq_of_isTypeFn
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:41:23.449437+00:00
-- url     : https://prove2.me/theorems/e7101ad1-72ce-4927-8602-33aa45c1ed3b
-- title:
--   Period Datum: two mul eq of is Type Fn
-- statement:
--   The Period Datum construction uses the two mul eq of is Type Fn property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/TwoMulEqOfIsTypeFn.lean#L67-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/TwoMulEqOfIsTypeFn.lean#L67-L81

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsEquivOfSumEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_HostGeneratorPowFourTraceNormModEight
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_TwoMulEqOfIsTypeFn
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped TensorProduct
open GlobalTheory GlobalTheory.PeriodDatum
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem GlobalTheory.PeriodDatum.two_mul_eq_of_isTypeFn (H : Host E) {p q g : ℕ} {ty : Fin g → (E →+* ℂ)} (hty : IsTypeFn H p q ty) :
    2 * g = Module.finrank ℚ E * (p + q) := by sorry
