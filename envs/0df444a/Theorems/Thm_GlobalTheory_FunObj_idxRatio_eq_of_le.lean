-- Prove2me | Theorems.Thm_GlobalTheory_FunObj_idxRatio_eq_of_le
-- name    : GlobalTheory.FunObj.idxRatio_eq_of_le
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T13:41:28.935551+00:00
-- url     : https://prove2.me/theorems/701e6e65-0481-469d-960e-335bf27d7a3f
-- title:
--   Fun Obj: idx Ratio eq of le
-- statement:
--   The Fun Obj construction uses the idx Ratio eq of le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/InverseUnipotentVolumeConjDiagonalUnitsGLMul.lean#L15-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/InverseUnipotentVolumeConjDiagonalUnitsGLMul.lean#L15-L23

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_FlatTensorVacuum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_InverseUnipotentVolumeConjDiagonalUnitsGLMul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.FunObj GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.RootEx
noncomputable section
open GlobalTheory GlobalTheory.FunObj
open Matrix
variable {G : Type*} [Group G]

theorem GlobalTheory.FunObj.idxRatio_eq_of_le {A B D : Subgroup G} (hD : D ≤ A ⊓ B) (h0 : D.relIndex (A ⊓ B) ≠ 0) :
    idxRatio A B = (D.relIndex A : ℚ) / D.relIndex B := by sorry
