-- Prove2me | Theorems.Thm_GlobalTheory_FrameBasic_cramer_last
-- name    : GlobalTheory.FrameBasic.cramer_last
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T13:36:11.122553+00:00
-- url     : https://prove2.me/theorems/28dafe17-be41-408e-a199-5fdf69134e2d
-- title:
--   Frame Basic: cramer last
-- statement:
--   The Frame Basic construction uses the cramer last property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/BasisOfIsCompl.lean#L155-L162
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/BasisOfIsCompl.lean#L155-L162

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_BasisOfIsCompl
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
open scoped Pointwise ENNReal Classical TensorProduct
open GlobalTheory GlobalTheory.FrameBasic
variable {E : Type} [CommRing E]

theorem GlobalTheory.FrameBasic.cramer_last {r : ℕ} (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (β : Fin (r + 1) → E) (c : E)
    (h : Z.mulVec β = Pi.single (Fin.last r) c) :
    Z.det * β (Fin.last r) = (Z.submatrix Fin.castSucc Fin.castSucc).det * c := by sorry
