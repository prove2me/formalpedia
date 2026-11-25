-- Prove2me | Theorems.Thm_GlobalTheory_HL_RatPat_rhoL_lt
-- name    : GlobalTheory.HL.RatPat.rhoL_lt
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T08:47:50.285551+00:00
-- url     : https://prove2.me/theorems/ef89ee7f-9c7f-4db0-894e-4daab22e8c52
-- title:
--   Rat Pat: rho L lt
-- statement:
--   The Rat Pat construction uses the rho L lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/BlockUnitriangularRationalFromCommonStabiliser.lean#L23-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/BlockUnitriangularRationalFromCommonStabiliser.lean#L23-L33

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

theorem GlobalTheory.HL.RatPat.rhoL_lt {R : Type} [CommRing R] (bs : List (Rˣ × ℕ+)) (a : ℕ)
    (ha : a < (bs.map (fun b => (b.2 : ℕ))).sum) : rhoL bs a < (bs.map (fun b => (b.2 : ℕ))).sum := by sorry
