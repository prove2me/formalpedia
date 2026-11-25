-- Prove2me | Theorems.Thm_GlobalTheory_HL_RatPat_rhoL_rhoL
-- name    : GlobalTheory.HL.RatPat.rhoL_rhoL
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T08:47:18.698708+00:00
-- url     : https://prove2.me/theorems/1455dc63-aa28-552d-95ed-dabf41b12b57
-- title:
--   Rat Pat: rho L rho L
-- statement:
--   The Rat Pat construction uses the rho L rho L property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/BlockUnitriangularRationalFromCommonStabiliser.lean#L35-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/BlockUnitriangularRationalFromCommonStabiliser.lean#L35-L47

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_PsiEDef
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_GFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianStabiliserRationalUnitriangularPairsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_RationalExtend
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_BlockUnitriangularRationalFromCommonStabiliser
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.RatPat

theorem GlobalTheory.HL.RatPat.rhoL_rhoL {R : Type} [CommRing R] (bs : List (Rˣ × ℕ+)) (a : ℕ)
    (ha : a < (bs.map (fun b => (b.2 : ℕ))).sum) : rhoL bs (rhoL bs a) = a := by sorry
