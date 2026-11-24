-- Prove2me | Theorems.Thm_GlobalTheory_FunObj_measurePreserving_piProdSplit
-- name    : GlobalTheory.FunObj.measurePreserving_piProdSplit
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T13:41:21.682469+00:00
-- url     : https://prove2.me/theorems/0a9d4287-b85d-4d55-a7e7-91beb206804a
-- title:
--   Fun Obj: measure Preserving pi Prod Split
-- statement:
--   The Fun Obj construction uses the measure Preserving pi Prod Split property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MeasurePreservingPiProdSplit.lean#L23-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MeasurePreservingPiProdSplit.lean#L23-L38

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_FlatTensorVacuum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MeasurePreservingPiProdSplit
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
open scoped NNReal ENNReal
noncomputable section
open GlobalTheory GlobalTheory.FunObj
open GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.RootEx
variable {ι : Type*} [Fintype ι] {α β γ : ι → Type*} [∀ i, MeasurableSpace (α i)] [∀ i, MeasurableSpace (β i)]
  [∀ i, MeasurableSpace (γ i)]

theorem GlobalTheory.FunObj.measurePreserving_piProdSplit (μ : ∀ i, Measure (α i)) (ν : ∀ i, Measure (β i)) [∀ i, SigmaFinite (μ i)]
    [∀ i, SigmaFinite (ν i)] : MeasurePreserving (piProdSplit α β) (.pi fun i => (μ i).prod (ν i))
      ((Measure.pi μ).prod (Measure.pi ν)) := by sorry
