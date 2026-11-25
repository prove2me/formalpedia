-- Prove2me | Theorems.Thm_GlobalTheory_HL_Inhab_isSD_stdLat
-- name    : GlobalTheory.HL.Inhab.isSD_stdLat
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T06:34:15.7077+00:00
-- url     : https://prove2.me/theorems/b66bf389-a539-47d2-9e30-400044ec1392
-- title:
--   Inhab: is SD std Lat
-- statement:
--   The Inhab construction uses the is SD std Lat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/HermitianFourInverseMul.lean#L266-L301
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/HermitianFourInverseMul.lean#L266-L301

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsIntegralIff
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianFourInverseMul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ValuativeRel Formalism.MainNotions.S.Loc
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.Inhab
open GlobalTheory.HL.Model
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]

theorem GlobalTheory.HL.Inhab.isSD_stdLat (L : LocE F E) {n : ℕ} (H K : Matrix (Fin n) (Fin n) E) (hH : IsIntM L H)
    (hK : IsIntM L K) (hKH : K * H = 1) : IsSD L H (stdLat L n) := by sorry
