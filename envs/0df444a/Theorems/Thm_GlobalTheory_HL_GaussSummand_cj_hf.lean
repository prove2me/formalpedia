-- Prove2me | Theorems.Thm_GlobalTheory_HL_GaussSummand_cj_hf
-- name    : GlobalTheory.HL.GaussSummand.cj_hf
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T06:23:15.916712+00:00
-- url     : https://prove2.me/theorems/2137a41a-f782-47c8-9118-20e29057d4db
-- title:
--   Gauss Summand: cj hf
-- statement:
--   The Gauss Summand construction uses the cj hf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/NormGaussSumLe.lean#L40-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/NormGaussSumLe.lean#L40-L44

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SqNormSumRepsMulIndexLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_NormGaussSumLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical ComplexConjugate
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.GaussSummand
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable (L : LocE F E) {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E)

theorem GlobalTheory.HL.GaussSummand.cj_hf (h : IsHerm L Hm) (x y : Fin n → E) : L.cj (hf L Hm x y) = hf L Hm y x := by sorry
