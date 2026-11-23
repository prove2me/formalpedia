-- Prove2me | Theorems.Thm_GlobalTheory_FrameBasic_det_mono
-- name    : GlobalTheory.FrameBasic.det_mono
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:51:50.494565+00:00
-- url     : https://prove2.me/theorems/3317dc54-aaa3-4d55-a22e-d6c61768c2d0
-- title:
--   Frame Basic: det mono
-- statement:
--   The Frame Basic construction uses the det mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/BasisOfIsCompl.lean#L79-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/BasisOfIsCompl.lean#L79-L88

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

theorem GlobalTheory.FrameBasic.det_mono {n : ℕ} (A : Matrix (Fin n) (Fin n) E) (σ : Fin n → Fin n)
    (h0 : ∀ a b, b ≠ σ a → A a b = 0) :
    A.det = (∏ a, A a (σ a)) * ((1 : Matrix (Fin n) (Fin n) E).submatrix σ id).det := by sorry
