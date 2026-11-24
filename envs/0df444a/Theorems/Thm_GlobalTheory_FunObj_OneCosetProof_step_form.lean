-- Prove2me | Theorems.Thm_GlobalTheory_FunObj_OneCosetProof_step_form
-- name    : GlobalTheory.FunObj.OneCosetProof.step_form
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T13:40:25.080803+00:00
-- url     : https://prove2.me/theorems/423673f5-0b5d-42d1-9482-af5ed8d14bb4
-- title:
--   One Coset Proof: step form
-- statement:
--   The One Coset Proof construction uses the step form property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/OneCosetOfIsTensor.lean#L227-L352
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/OneCosetOfIsTensor.lean#L227-L352

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

theorem GlobalTheory.FunObj.OneCosetProof.step_form [ν.IsAddHaarMeasure] (hs : 1 ≤ G.s) (hψ : HasConductor ψ 1)
    (hT : G.IsTensor ϖ e (oppositePath G.m) T) (g : G.VertexGroup)
    (x : ColArgs G) (y : RowArgs G) (h : flatTensor hs ψ ν (moved G false g T) x y ≠ 0) (j : Fin (G.m - 1))
    (hj : frameGL (src_eq hs j) (g (G.m, j)) = diagGL (Sum.elim (fun _ => 1) fun p => ϖ ^ (e * (p.val + 1)))) :
    ∃ r ∈ symR k _ _, ∃ w ∈ KO k _, frameGL (tgt_eq hs j) (g (G.m, j + 1)) =
      r * diagGL (Sum.elim (fun _ => 1) fun p => ϖ ^ (e * (p.val + 1))) * w := by sorry
