-- Prove2me | Theorems.Thm_GlobalTheory_FrameBasic_det_mono_unit
-- name    : GlobalTheory.FrameBasic.det_mono_unit
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T13:36:21.621229+00:00
-- url     : https://prove2.me/theorems/0379910b-79f8-405a-ac75-9331d8c18b9a
-- title:
--   Frame Basic: det mono unit
-- statement:
--   The Frame Basic construction uses the det mono unit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/BasisOfIsCompl.lean#L98-L110
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/BasisOfIsCompl.lean#L98-L110

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

theorem GlobalTheory.FrameBasic.det_mono_unit {n : ℕ} (A : Matrix (Fin n) (Fin n) E) (σ : Fin n → Fin n)
    (h0 : ∀ a b, b ≠ σ a → A a b = 0) (hu : ∀ a, A a (σ a) ≠ 0 → IsUnit (A a (σ a)))
    (hd : A.det ≠ 0) : IsUnit A.det := by sorry
