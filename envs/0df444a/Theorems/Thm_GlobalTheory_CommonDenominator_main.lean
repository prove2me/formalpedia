-- Prove2me | Theorems.Thm_GlobalTheory_CommonDenominator_main
-- name    : GlobalTheory.CommonDenominator.main
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T06:08:29.34286+00:00
-- url     : https://prove2.me/theorems/7d1b57e3-92d5-5ada-9f1b-d0e5796b9f6c
-- title:
--   Common Denominator: main
-- statement:
--   The Common Denominator construction uses the main property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/AlgebraMapMemO.lean#L32-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/AlgebraMapMemO.lean#L32-L66

import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_AlgebraMapMemO
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel
open GlobalTheory GlobalTheory.CommonDenominator
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]

theorem GlobalTheory.CommonDenominator.main (L : Formalism.MainNotions.S.Loc.LocE F E) {n : ℕ} [IsNonarchimedeanLocalField F]
    {Λ : Submodule (↥(Formalism.MainNotions.S.Loc.LocE.O L)) (Fin n → E)} (hΛ : GlobalTheory.HL.IsLat L Λ)
    (x : Fin n → E) :
    ∃ (t : ↥(Valuation.integer (ValuativeRel.valuation F))),
      t ≠ (0 : ↥(Valuation.integer (ValuativeRel.valuation F))) ∧
      (Algebra.algebraMap F E : F → E) (↑t : F) • x ∈ Λ := by sorry
