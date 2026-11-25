-- Prove2me | Theorems.Thm_GlobalTheory_FrameGram_submatrix_mul_upper
-- name    : GlobalTheory.FrameGram.submatrix_mul_upper
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T07:28:10.852446+00:00
-- url     : https://prove2.me/theorems/f990cae8-8236-4f02-be62-9b5ed654b66a
-- title:
--   Frame Gram: submatrix mul upper
-- statement:
--   The Frame Gram construction uses the submatrix mul upper property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/FrameLatticeGramDetAndMinorsOrbitInvariant.lean#L16-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/FrameLatticeGramDetAndMinorsOrbitInvariant.lean#L16-L29

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsEqZpowMulUnit
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_BasisOfIsCompl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_DetGramTwoFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_FrameUnipotentUnitriangular
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_FrameLatticeGramDetAndMinorsOrbitInvariant
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.FrameGram

theorem GlobalTheory.FrameGram.submatrix_mul_upper {E : Type} [CommRing E] {N m : ℕ} (hm : m ≤ N) {ι : Type} (f : ι → Fin N)
    (M B : Matrix (Fin N) (Fin N) E) (hB : ∀ i j, j < i → B i j = 0) :
    (M * B).submatrix f (Fin.castLE hm) =
      M.submatrix f (Fin.castLE hm) * B.submatrix (Fin.castLE hm) (Fin.castLE hm) := by sorry
