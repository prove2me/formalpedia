-- Prove2me | Theorems.Thm_GlobalTheory_FrameBasic_det_perm_unit
-- name    : GlobalTheory.FrameBasic.det_perm_unit
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:52:11.795931+00:00
-- url     : https://prove2.me/theorems/f657f613-6e48-41f1-b6da-355b2c894e40
-- title:
--   Frame Basic: det perm unit
-- statement:
--   The Frame Basic construction uses the det perm unit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/BasisOfIsCompl.lean#L90-L96
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/BasisOfIsCompl.lean#L90-L96

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

theorem GlobalTheory.FrameBasic.det_perm_unit {n : ℕ} (σ : Fin n → Fin n) (h : Function.Injective σ) :
    IsUnit ((1 : Matrix (Fin n) (Fin n) E).submatrix σ id).det := by sorry
