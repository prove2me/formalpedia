-- Prove2me | Theorems.Thm_GlobalTheory_FunObj_OneCosetProof_moved_shift
-- name    : GlobalTheory.FunObj.OneCosetProof.moved_shift
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T13:43:07.650464+00:00
-- url     : https://prove2.me/theorems/79bc78ee-9580-4d17-98c5-f595aea0f734
-- title:
--   One Coset Proof: moved shift
-- statement:
--   The One Coset Proof construction uses the moved shift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/OneCosetOfIsTensor.lean#L139-L179
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/OneCosetOfIsTensor.lean#L139-L179

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

theorem GlobalTheory.FunObj.OneCosetProof.moved_shift (hs : 1 ≤ G.s) (hT : G.IsTensor ϖ e (oppositePath G.m) T) (g : G.VertexGroup) (x : ColArgs G)
    (y : RowArgs G) (v : Vars G) (Y : Shift G)
    (hY : ∀ j r s, ¬ Free ((G.m - 2 - j.val) / 2 + 1) (r, s) → Y j r s = 0)
    (hL : ∀ (j : Fin (G.m - 1)) r s, valuation k ((((frameGL (tgt_eq hs j) (g (G.m, j + 1)))⁻¹).val * Y j *
      (frameGL (src_eq hs j) (g (G.m, j))).val) r s) ≤ valuation k ((ϖ ^ e : kˣ) : k)) :
    moved G false g T (fill hs x y (v + Y.vars)) = moved G false g T (fill hs x y v) := by sorry
