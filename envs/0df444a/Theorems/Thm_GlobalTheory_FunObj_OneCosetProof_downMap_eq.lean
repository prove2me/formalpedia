-- Prove2me | Theorems.Thm_GlobalTheory_FunObj_OneCosetProof_downMap_eq
-- name    : GlobalTheory.FunObj.OneCosetProof.downMap_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:31:13.560287+00:00
-- url     : https://prove2.me/theorems/71f83c14-26a3-4999-b018-f4ad768d6b36
-- title:
--   One Coset Proof: down Map eq
-- statement:
--   The One Coset Proof construction uses the down Map eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/OneCosetOfIsTensor.lean#L105-L108
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/OneCosetOfIsTensor.lean#L105-L108

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_FlatTensorVacuum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsKOOfDet
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_OneCosetOfIsTensor
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
open scoped NNReal ENNReal Pointwise
noncomputable section
open GlobalTheory GlobalTheory.FunObj GlobalTheory.FunObj.OneCosetProof
open GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.RootEx GlobalTheory.FunObj
variable {k : Type} [Field k]
variable {G : Grid k}

theorem GlobalTheory.FunObj.OneCosetProof.downMap_eq (hs : 1 ≤ G.s) (x : ColArgs G) (e : Vars G) (j : Fin (G.m - 1)) : downMap hs x e j =
    (stepPt (x j) (e j)).reindex (frame (tgt_eq hs j)) (frame (src_eq hs j)) := by sorry
