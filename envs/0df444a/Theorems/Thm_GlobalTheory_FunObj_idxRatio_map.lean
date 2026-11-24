-- Prove2me | Theorems.Thm_GlobalTheory_FunObj_idxRatio_map
-- name    : GlobalTheory.FunObj.idxRatio_map
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T13:41:39.532679+00:00
-- url     : https://prove2.me/theorems/b0144d8b-12c7-43d0-ac33-61bc14eceb68
-- title:
--   Fun Obj: idx Ratio map
-- statement:
--   The Fun Obj construction uses the idx Ratio map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/InverseUnipotentVolumeConjDiagonalUnitsGLMul.lean#L25-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/InverseUnipotentVolumeConjDiagonalUnitsGLMul.lean#L25-L28

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

theorem GlobalTheory.FunObj.idxRatio_map {f : G →* G} (hf : Function.Injective f) (A B : Subgroup G) :
    idxRatio (A.map f) (B.map f) = idxRatio A B := by sorry
