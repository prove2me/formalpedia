-- Prove2me | Theorems.Thm_GlobalTheory_FunObj_flatTensor_pureTensor
-- name    : GlobalTheory.FunObj.flatTensor_pureTensor
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T13:41:53.237638+00:00
-- url     : https://prove2.me/theorems/b096034d-3471-4b45-b705-4b515c74c50f
-- title:
--   Fun Obj: flat Tensor pure Tensor
-- statement:
--   The Fun Obj construction uses the flat Tensor pure Tensor property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MeasurePreservingPiProdSplit.lean#L292-L328
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MeasurePreservingPiProdSplit.lean#L292-L328

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
variable {k : Type*} [Field k] (G : Grid k)
variable {G}
variable (hs : 1 ≤ G.s)
variable [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable [MeasurableSpace k] [BorelSpace k] (ψ : AddChar k Circle) (ν : Measure k)
variable {ψ}

theorem GlobalTheory.FunObj.flatTensor_pureTensor [ν.IsAddHaarMeasure] (hm : 0 < G.m) (hψ : Continuous ψ)
    (φ : ∀ b : Edge, Matrix (Fin (G.rank b.tgt)) (Fin (G.rank b.src)) k → ℂ)
    (hφ : ∀ j < G.m - 1, φ (.theta G.m j) ∈ SB _) (x : ColArgs G) (y : RowArgs G) :
    Integrable (flatIntegrand hs ψ (G.lines₂ (oppositePath G.m) φ) x y) (varsVol G ν) ∧
    Integrable (contractIntegrand hs ψ ν φ x) (keptVol G ν) ∧
    flatTensor hs ψ ν (G.lines₂ (oppositePath G.m) φ) x y =
      (∏ i ∈ Finset.range G.m, φ (.ex i G.m) (y i)ᵀ) * φ (.theta G.m (G.m - 1)) (lastMap hs hm x)ᵀ *
        ∫ w, contractIntegrand hs ψ ν φ x w ∂(keptVol G ν) := by sorry
