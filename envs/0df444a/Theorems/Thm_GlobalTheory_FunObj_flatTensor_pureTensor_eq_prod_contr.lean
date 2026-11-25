-- Prove2me | Theorems.Thm_GlobalTheory_FunObj_flatTensor_pureTensor_eq_prod_contr
-- name    : GlobalTheory.FunObj.flatTensor_pureTensor_eq_prod_contr
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T12:06:26.539296+00:00
-- url     : https://prove2.me/theorems/0017cf50-1104-4f9c-8d73-4c90679e97fd
-- title:
--   Fun Obj: flat Tensor pure Tensor eq prod contr
-- statement:
--   The Fun Obj construction uses the flat Tensor pure Tensor eq prod contr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/FlatTensorPureTensorEqProdContr.lean#L282-L337
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/FlatTensorPureTensorEqProdContr.lean#L282-L337

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MeasurePreservingPiProdSplit
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_ContrFactor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_FlatMapsPreserveSchwartzBruhatAndSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_FlatTensorPureTensorEqProdContr
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
noncomputable section
open GlobalTheory GlobalTheory.FunObj
open GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.RootEx GlobalTheory.LocFlat

theorem GlobalTheory.FunObj.flatTensor_pureTensor_eq_prod_contr : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (G : Grid k) (hs : 1 ≤ G.s) (hm : 2 ≤ G.m), Even G.m → ∀ (ψ : AddChar k Circle) (ν : Measure k), Continuous ψ → ψ ≠ 1 → ν.IsAddHaarMeasure → ∀ (φ : ∀ b : Edge, Matrix (Fin (G.rank b.tgt)) (Fin (G.rank b.src)) k → ℂ), (∀ j < G.m - 1, φ (.theta G.m j) ∈ SB _) → ∀ (x : ColArgs G) (y : RowArgs G), flatTensor hs ψ ν (G.lines₂ (oppositePath G.m) φ) x y = (∏ i ∈ Finset.range G.m, φ (.ex i G.m) (y i)ᵀ) * (φ (.theta G.m (G.m - 1)) (lastMap hs (by omega) x)ᵀ * GlobalTheory.StepData.hat ψ ν (-1) (fun u => flCol ψ ν 1 (stepDatum hs φ ⟨G.m - 2, by omega⟩) (fromCols (x (G.m - 2)) (Matrix.of fun r _ => u r))) (x (G.m - 2 + 1) (topLast G (G.m - 2 + 1 + 1)))) * ∏ j : Fin (G.m - 2), if Even j.1 then contr ψ ν (flCol ψ ν ((G.m - 2 - j) / 2 + 1) (stepDatum hs φ ⟨j, by omega⟩)) (flRow ψ ν ((G.m - 2 - (j + 1)) / 2 + 1) (stepDatum hs φ ⟨j + 1, by omega⟩)) (x j, x (j + 1)) else 1 := by sorry
