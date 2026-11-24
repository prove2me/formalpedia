-- Prove2me | Theorems.Thm_GlobalTheory_FunObj_OneCosetProof_moveArgs_add
-- name    : GlobalTheory.FunObj.OneCosetProof.moveArgs_add
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T13:42:53.442899+00:00
-- url     : https://prove2.me/theorems/4b53148d-9a9c-488c-af47-3dcc9918fbac
-- title:
--   One Coset Proof: move Args add
-- statement:
--   The One Coset Proof construction uses the move Args add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/OneCosetOfIsTensor.lean#L88-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/OneCosetOfIsTensor.lean#L88-L91

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

theorem GlobalTheory.FunObj.OneCosetProof.moveArgs_add (g : G.VertexGroup) (z z' : G.Args) :
    G.moveArgs .one g (z + z') = G.moveArgs .one g z + G.moveArgs .one g z' := by sorry
