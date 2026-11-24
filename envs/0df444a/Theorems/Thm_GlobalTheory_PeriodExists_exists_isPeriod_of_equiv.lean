-- Prove2me | Theorems.Thm_GlobalTheory_PeriodExists_exists_isPeriod_of_equiv
-- name    : GlobalTheory.PeriodExists.exists_isPeriod_of_equiv
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T18:42:50.286118+00:00
-- url     : https://prove2.me/theorems/ba4c1436-7104-4fee-a735-e81fca701ed9
-- title:
--   Period Exists: exists is Period of equiv
-- statement:
--   The Period Exists construction uses the exists is Period of equiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/TypeFnPeriodExistModuliNonempty.lean#L48-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/TypeFnPeriodExistModuliNonempty.lean#L48-L82

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

theorem GlobalTheory.PeriodExists.exists_isPeriod_of_equiv {H : Host E} {D : Datum H} {g g' : ℕ} {ty : Fin g → (E →+* ℂ)}
    {ty' : Fin g' → (E →+* ℂ)} (e : Fin g ≃ Fin g') (he : ∀ k, ty' (e k) = ty k)
    {P : D.La →+ (Fin g' → ℂ)} (hP : IsPeriod D ty' P) : ∃ P', IsPeriod D ty P' := by sorry
