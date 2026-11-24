-- Prove2me | Theorems.Thm_GlobalTheory_FunObj_invVol_eq_idxRatio
-- name    : GlobalTheory.FunObj.invVol_eq_idxRatio
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T13:41:12.737872+00:00
-- url     : https://prove2.me/theorems/01ad901d-4936-4a29-b181-e05d823fd0ca
-- title:
--   Fun Obj: inv Vol eq idx Ratio
-- statement:
--   The Fun Obj construction uses the inv Vol eq idx Ratio property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/InverseUnipotentVolumeConjDiagonalUnitsGLMul.lean#L123-L128
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/InverseUnipotentVolumeConjDiagonalUnitsGLMul.lean#L123-L128

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
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n : Type} [Fintype n] [DecidableEq n] {c : ℕ}
omit [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem GlobalTheory.FunObj.invVol_eq_idxRatio (C : Subgroup (GL (n ⊕ Fin c) k)) :
    invVol C = idxRatio (symN k n c ⊓ KO k _) (symN k n c ⊓ C) := by sorry
