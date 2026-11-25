-- Prove2me | Theorems.Thm_GlobalTheory_HL_RatPat_det_ne_zero_of_monomial
-- name    : GlobalTheory.HL.RatPat.det_ne_zero_of_monomial
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T08:42:43.073239+00:00
-- url     : https://prove2.me/theorems/30c2ad48-1f6d-4e19-86a3-e102461c9805
-- title:
--   Rat Pat: det ne zero of monomial
-- statement:
--   The Rat Pat construction uses the det ne zero of monomial property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/BlockUnitriangularRationalFromCommonStabiliser.lean#L113-L135
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/BlockUnitriangularRationalFromCommonStabiliser.lean#L113-L135

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

theorem GlobalTheory.HL.RatPat.det_ne_zero_of_monomial {K : Type} [Field K] {m : ℕ} (M : Matrix (Fin m) (Fin m) K)
    (σ : Equiv.Perm (Fin m)) (hM : ∀ a b, M a b ≠ 0 ↔ b = σ a) : M.det ≠ 0 := by sorry
