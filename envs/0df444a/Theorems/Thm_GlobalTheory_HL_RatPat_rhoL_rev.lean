-- Prove2me | Theorems.Thm_GlobalTheory_HL_RatPat_rhoL_rev
-- name    : GlobalTheory.HL.RatPat.rhoL_rev
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T08:41:37.760458+00:00
-- url     : https://prove2.me/theorems/32cdbffe-972f-4807-9c03-ced556568bd0
-- title:
--   Rat Pat: rho L rev
-- statement:
--   The Rat Pat construction uses the rho L rev property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/BlockUnitriangularRationalFromCommonStabiliser.lean#L74-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/BlockUnitriangularRationalFromCommonStabiliser.lean#L74-L95

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

theorem GlobalTheory.HL.RatPat.rhoL_rev {R : Type} [CommRing R] (bs : List (Rˣ × ℕ+)) (x y : ℕ) (hxy : x < y)
    (hy : y < (bs.map (fun b => (b.2 : ℕ))).sum)
    (hB : ∀ l : ℕ, x < l → l ≤ y → ¬ ∀ a, a < l → rhoL bs a < l) : rhoL bs y < rhoL bs x := by sorry
