-- Prove2me | Theorems.Thm_GlobalTheory_FunObj_OneCosetProof_mem_rowR
-- name    : GlobalTheory.FunObj.OneCosetProof.mem_rowR
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T13:42:35.836599+00:00
-- url     : https://prove2.me/theorems/5992a61b-157e-4f98-b5af-22d8d9731fb0
-- title:
--   One Coset Proof: mem row R
-- statement:
--   The One Coset Proof construction uses the mem row R property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/OneCosetOfIsTensor.lean#L367-L373
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/OneCosetOfIsTensor.lean#L367-L373

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
variable [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {ϖ : kˣ} {e : ℕ} {T : G.Args → ℂ}
variable [MeasurableSpace k] [BorelSpace k] {ψ : AddChar k Circle} {ν : Measure k}
omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k]

theorem GlobalTheory.FunObj.OneCosetProof.mem_rowR (hs : 1 ≤ G.s) {j c : ℕ} (hj : j < G.m) (h : topRank G j + c = G.rank (G.m, j))
    {g : GL (Fin (G.rank (G.m, j))) k} (hg : frameGL h g ∈ symR k _ c) : g ∈ rowR hs hj := by sorry
