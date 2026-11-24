-- Prove2me | Theorems.Thm_GlobalTheory_PeriodExists_exists_equiv_of_isTypeFn
-- name    : GlobalTheory.PeriodExists.exists_equiv_of_isTypeFn
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T18:43:48.49967+00:00
-- url     : https://prove2.me/theorems/c9616777-044f-4d92-bb76-052274edb7bb
-- title:
--   Period Exists: exists equiv of is Type Fn
-- statement:
--   The Period Exists construction uses the exists equiv of is Type Fn property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/TypeFnPeriodExistModuliNonempty.lean#L37-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/TypeFnPeriodExistModuliNonempty.lean#L37-L46

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

theorem GlobalTheory.PeriodExists.exists_equiv_of_isTypeFn {H : Host E} {p q g g' : ℕ} {ty : Fin g → (E →+* ℂ)}
    {ty' : Fin g' → (E →+* ℂ)} (h : IsTypeFn H p q ty) (h' : IsTypeFn H p q ty') :
    ∃ e : Fin g ≃ Fin g', ∀ k, ty' (e k) = ty k := by sorry
