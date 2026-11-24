-- Prove2me | Theorems.Thm_GlobalTheory_FunObj_OneCosetProof_support_step
-- name    : GlobalTheory.FunObj.OneCosetProof.support_step
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T13:40:08.284409+00:00
-- url     : https://prove2.me/theorems/fc8ecd23-1623-46e6-9a2a-676756a471f3
-- title:
--   One Coset Proof: support step
-- statement:
--   The One Coset Proof construction uses the support step property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/OneCosetOfIsTensor.lean#L113-L129
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/OneCosetOfIsTensor.lean#L113-L129

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

theorem GlobalTheory.FunObj.OneCosetProof.support_step (hs : 1 ≤ G.s) (hT : G.IsTensor ϖ e (oppositePath G.m) T) (g : G.VertexGroup) (x : ColArgs G)
    (y : RowArgs G) (v : Vars G) (h : moved G false g T (fill hs x y v) ≠ 0) (j : Fin (G.m - 1)) (r s) :
    (((frameGL (tgt_eq hs j) (g (G.m, j + 1)))⁻¹).val * stepPt (x j) (v j) *
      (frameGL (src_eq hs j) (g (G.m, j))).val) r s ∈ 𝒪[k] := by sorry
