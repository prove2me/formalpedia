-- Prove2me | Theorems.Thm_GlobalTheory_SplitFlip_FourierDepth_fourier_exchange
-- name    : GlobalTheory.SplitFlip.FourierDepth.fourier_exchange
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T12:25:47.919097+00:00
-- url     : https://prove2.me/theorems/f527c4a7-c8a6-4ca1-8c3b-f415a2e65289
-- title:
--   Fourier Depth: fourier exchange
-- statement:
--   The Fourier Depth construction uses the fourier exchange property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MemMatLatSmulBlockLat.lean#L140-L145
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MemMatLatSmulBlockLat.lean#L140-L145

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

theorem GlobalTheory.SplitFlip.FourierDepth.fourier_exchange (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (A D : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D]
    (ψ : AddChar k Circle) (ϖ : kˣ) (e : ℕ) (P : Finset D) (hϖ : IsUnif ϖ) (hψ : HasConductor ψ 1) :
    (∀ Φ : Matrix A D k → ℂ, IsNatDatum ϖ e Φ → HasDepth ϖ e (blockLat ϖ e P) (fourierSum ψ ϖ e P Φ)) ∧
      ∀ Ψ : Matrix A D k → ℂ, HasDepth ϖ e (blockLat ϖ e P) Ψ → IsNatDatum ϖ e (invFourierSum ψ ϖ e P Ψ) := by sorry
