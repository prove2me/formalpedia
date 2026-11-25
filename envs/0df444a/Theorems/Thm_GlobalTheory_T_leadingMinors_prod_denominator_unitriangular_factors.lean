-- Prove2me | Theorems.Thm_GlobalTheory_T_leadingMinors_prod_denominator_unitriangular_factors
-- name    : GlobalTheory.T.leadingMinors_prod_denominator_unitriangular_factors
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T07:46:00.738072+00:00
-- url     : https://prove2.me/theorems/a1885b04-0212-4ea5-b9b5-3fce2864dc6c
-- title:
--   T: leading Minors prod denominator unitriangular factors
-- statement:
--   The T construction uses the leading Minors prod denominator unitriangular factors property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/LeadingMinorsProdDenominatorUnitriangularFactorsStatement.lean#L10-L11
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/LeadingMinorsProdDenominatorUnitriangularFactorsStatement.lean#L10-L11

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_LeadingMinorsProdDenominatorUnitriangularFactors
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_HermLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_LeadingMinorsProdDenominatorUnitriangularFactorsStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.leadingMinors_prod_denominator_unitriangular_factors : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ u u' : Matrix (Fin (r + 1)) (Fin (r + 1)) E, IsUni u → IsUni u' → (∀ i j : Fin (r + 1), sameBlock S.w.blocks i j = true → u i j ∈ L.O) → IsIntM L (cT L u * S.Zh * u') → ∀ Δ : E, Δ = ∏ l : Fin (r + 2), (if S.D l ≠ 0 then S.D l else 1) → Δ ∈ L.O ∧ IsUnit Δ ∧ vE L S.ϖ (Δ * L.cj Δ) = S.vD ∧ ∀ i j, L.cj Δ * u i j ∈ L.O ∧ Δ * u' i j ∈ L.O := by sorry
