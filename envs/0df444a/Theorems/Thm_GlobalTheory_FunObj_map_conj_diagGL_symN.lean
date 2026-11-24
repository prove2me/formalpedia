-- Prove2me | Theorems.Thm_GlobalTheory_FunObj_map_conj_diagGL_symN
-- name    : GlobalTheory.FunObj.map_conj_diagGL_symN
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T13:41:27.011667+00:00
-- url     : https://prove2.me/theorems/f2248c07-57a6-408f-9429-c84c4901d20f
-- title:
--   Fun Obj: map conj diag GL sym N
-- statement:
--   The Fun Obj construction uses the map conj diag GL sym N property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/InverseUnipotentVolumeConjDiagonalUnitsGLMul.lean#L92-L104
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/InverseUnipotentVolumeConjDiagonalUnitsGLMul.lean#L92-L104

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
variable {k : Type} [Field k] {n : Type} [Fintype n] [DecidableEq n] {c : ℕ}

theorem GlobalTheory.FunObj.map_conj_diagGL_symN (d : n ⊕ Fin c → kˣ) :
    (symN k n c).map (MulAut.conj (diagGL d)).toMonoidHom = symN k n c := by sorry
