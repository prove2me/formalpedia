-- Prove2me | Theorems.Thm_GlobalTheory_FunObj_map_conj_diagGL_N_le
-- name    : GlobalTheory.FunObj.map_conj_diagGL_N_le
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T13:41:13.766586+00:00
-- url     : https://prove2.me/theorems/f2973ef5-4eaf-4927-b7db-dbf6a8ba46a6
-- title:
--   Fun Obj: map conj diag GL N le
-- statement:
--   The Fun Obj construction uses the map conj diag GL N le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/InverseUnipotentVolumeConjDiagonalUnitsGLMul.lean#L85-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/InverseUnipotentVolumeConjDiagonalUnitsGLMul.lean#L85-L90

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

theorem GlobalTheory.FunObj.map_conj_diagGL_N_le (p : ℕ) (d : n ⊕ Fin c → kˣ) :
    (N k n c p).map (MulAut.conj (diagGL d)).toMonoidHom ≤ N k n c p := by sorry
