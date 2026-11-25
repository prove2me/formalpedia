-- Prove2me | Theorems.Thm_GlobalTheory_PeriodExists_typeFn_period_exist
-- name    : GlobalTheory.PeriodExists.typeFn_period_exist
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:51:30.152804+00:00
-- url     : https://prove2.me/theorems/48ab0e11-c72f-42f5-b120-1e05d8b024ef
-- title:
--   Period Exists: type Fn period exist
-- statement:
--   The Period Exists construction uses the type Fn period exist property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/TypeFnPeriodExistModuliNonempty.lean#L152-L165
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/TypeFnPeriodExistModuliNonempty.lean#L152-L165

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsHermCoordOfDatum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_SignatureHermitianModelOfDatumStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_HermFormConjDiag
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_TypeFnPeriodExistModuliNonempty
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix
open scoped nonZeroDivisors ComplexConjugate
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.PeriodExists
variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem GlobalTheory.PeriodExists.typeFn_period_exist : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H), (∃ (g : ℕ) (ty : Fin g → (E →+* ℂ)), IsTypeFn H D.p D.q ty) ∧ (∀ (g : ℕ) (ty : Fin g → (E →+* ℂ)), IsTypeFn H D.p D.q ty → g = Module.finrank ℚ E / 2 * (D.p + D.q) ∧ ∃ P, IsPeriod D ty P) ∧ (N1c → 1 ≤ D.p + D.q → ∀ (l : Level H) (Xo : Moduli D l) (c : Coeff l), Nonempty (Xo.XF c)) := by sorry
