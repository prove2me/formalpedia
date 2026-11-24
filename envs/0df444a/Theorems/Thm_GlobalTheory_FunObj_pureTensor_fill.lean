-- Prove2me | Theorems.Thm_GlobalTheory_FunObj_pureTensor_fill
-- name    : GlobalTheory.FunObj.pureTensor_fill
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T14:04:28.433868+00:00
-- url     : https://prove2.me/theorems/c3f2f176-481c-4499-87d9-02e1f096e115
-- title:
--   Fun Obj: pure Tensor fill
-- statement:
--   The Fun Obj construction uses the pure Tensor fill property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MeasurePreservingPiProdSplit.lean#L237-L252
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MeasurePreservingPiProdSplit.lean#L237-L252

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

theorem GlobalTheory.FunObj.pureTensor_fill (hm : 0 < G.m) (φ : ∀ b : Edge, Matrix (Fin (G.rank b.tgt)) (Fin (G.rank b.src)) k → ℂ)
    (x : ColArgs G) (y : RowArgs G) (e : Vars G) :
    G.lines₂ (oppositePath G.m) φ (fill hs x y e) = (∏ i ∈ Finset.range G.m, φ (.ex i G.m) (y i)ᵀ) *
      φ (.theta G.m (G.m - 1)) (lastMap hs hm x)ᵀ * ∏ j : Fin (G.m - 1), stepDatum hs φ j (stepPt (x j) (e j)) := by sorry
