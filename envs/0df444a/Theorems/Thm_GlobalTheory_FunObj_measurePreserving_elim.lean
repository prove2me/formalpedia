-- Prove2me | Theorems.Thm_GlobalTheory_FunObj_measurePreserving_elim
-- name    : GlobalTheory.FunObj.measurePreserving_elim
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T13:41:32.596369+00:00
-- url     : https://prove2.me/theorems/c85f12ab-2ab3-4c44-a517-fbd56e6f2f04
-- title:
--   Fun Obj: measure Preserving elim
-- statement:
--   The Fun Obj construction uses the measure Preserving elim property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MeasurePreservingPiProdSplit.lean#L70-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MeasurePreservingPiProdSplit.lean#L70-L79

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

theorem GlobalTheory.FunObj.measurePreserving_elim {A B C k : Type*} [Fintype A] [Fintype B] [Fintype C] [MeasurableSpace k]
    (ν : Measure k) [SigmaFinite ν] (e : A ⊕ B ≃ C) :
    MeasurePreserving (fun (p : (A → k) × (B → k)) c => Sum.elim p.1 p.2 (e.symm c))
      ((Measure.pi fun _ => ν).prod (Measure.pi fun _ => ν)) (Measure.pi fun _ => ν) := by sorry
