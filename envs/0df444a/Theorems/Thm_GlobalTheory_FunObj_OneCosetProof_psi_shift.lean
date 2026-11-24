-- Prove2me | Theorems.Thm_GlobalTheory_FunObj_OneCosetProof_psi_shift
-- name    : GlobalTheory.FunObj.OneCosetProof.psi_shift
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T13:40:22.846026+00:00
-- url     : https://prove2.me/theorems/2be704c3-ec96-4a28-a214-1d7645dd7103
-- title:
--   One Coset Proof: psi shift
-- statement:
--   The One Coset Proof construction uses the psi shift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/OneCosetOfIsTensor.lean#L183-L225
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/OneCosetOfIsTensor.lean#L183-L225

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

theorem GlobalTheory.FunObj.OneCosetProof.psi_shift [ν.IsAddHaarMeasure] (hs : 1 ≤ G.s) (hT : G.IsTensor ϖ e (oppositePath G.m) T) (g : G.VertexGroup)
    (x : ColArgs G) (y : RowArgs G) (h : flatTensor hs ψ ν (moved G false g T) x y ≠ 0) (Y : Shift G)
    (hY : ∀ j r s, ¬ Free ((G.m - 2 - j.val) / 2 + 1) (r, s) → Y j r s = 0) (hX : ∀ j r s, Y j r (.inl s) = 0)
    (hL : ∀ (j : Fin (G.m - 1)) r s, valuation k ((((frameGL (tgt_eq hs j) (g (G.m, j + 1)))⁻¹).val * Y j *
      (frameGL (src_eq hs j) (g (G.m, j))).val) r s) ≤ valuation k ((ϖ ^ e : kˣ) : k)) :
    ψ (∑ j, ch (Y j)) = 1 := by sorry
