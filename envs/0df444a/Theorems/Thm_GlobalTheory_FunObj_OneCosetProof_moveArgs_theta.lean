-- Prove2me | Theorems.Thm_GlobalTheory_FunObj_OneCosetProof_moveArgs_theta
-- name    : GlobalTheory.FunObj.OneCosetProof.moveArgs_theta
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:32:00.58174+00:00
-- url     : https://prove2.me/theorems/e80fabcd-ca5a-4674-a895-eb2168d4df42
-- title:
--   One Coset Proof: move Args theta
-- statement:
--   The One Coset Proof construction uses the move Args theta property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/OneCosetOfIsTensor.lean#L83-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/OneCosetOfIsTensor.lean#L83-L86

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

theorem GlobalTheory.FunObj.OneCosetProof.moveArgs_theta (g : G.VertexGroup) (z : G.Args) (i j : ℕ) : G.moveArgs .one g z (.theta i j) =
    (((g (i, j + 1))⁻¹).val * (z (.theta i j))ᵀ * (g (i, j)).val)ᵀ := by sorry
