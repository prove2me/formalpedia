-- Prove2me | Theorems.Thm_GlobalTheory_SplitFlip_FourierDepth_hasDepth_fourierSum
-- name    : GlobalTheory.SplitFlip.FourierDepth.hasDepth_fourierSum
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T20:20:01.248129+00:00
-- url     : https://prove2.me/theorems/bd9c47b2-3536-4e69-b904-f75c878ab4d2
-- title:
--   Fourier Depth: has Depth fourier Sum
-- statement:
--   The Fourier Depth construction uses the has Depth fourier Sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MemMatLatSmulBlockLat.lean#L71-L99
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MemMatLatSmulBlockLat.lean#L71-L99

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemMatLatSmulBlockLat
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory GlobalTheory.SplitFlip GlobalTheory.SplitWeil ValuativeRel
open scoped Pointwise
noncomputable section
open GlobalTheory GlobalTheory.SplitFlip GlobalTheory.SplitFlip.FourierDepth
variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {A D : Type*} [DecidableEq D]
variable [Fintype A] [DecidableEq A]

theorem GlobalTheory.SplitFlip.FourierDepth.hasDepth_fourierSum {ψ : AddChar k Circle} {ϖ : kˣ} (hϖ : IsUnif ϖ) (hψ : HasConductor ψ 1) (e : ℕ)
    (P : Finset D) {Φ : Matrix A D k → ℂ} (hΦ : IsNatDatum ϖ e Φ) :
    HasDepth ϖ e (blockLat ϖ e P) (fourierSum ψ ϖ e P Φ) := by sorry
