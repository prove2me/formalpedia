-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_AnalyticWord_bnd_succ_le
-- name    : GlobalTheory.CompanionTheory.AnalyticWord.bnd_succ_le
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T11:18:04.136854+00:00
-- url     : https://prove2.me/theorems/67d12656-061a-48e4-8ed7-6865ee9b6ff0
-- title:
--   Analytic Word: bnd succ le
-- statement:
--   The Analytic Word construction uses the bnd succ le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/SkewAdjointCasimirSpectral.lean#L251-L283
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/SkewAdjointCasimirSpectral.lean#L251-L283

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SkewAdjointCasimirSpectral
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.AnalyticWord
variable {V H : Type} [AddCommGroup V] [Module ℂ V] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {ι : Type}
variable [Fintype ι] (j : V →ₗ[ℂ] H) (Z : ι → Module.End ℂ V) {m : ℕ} (y : Fin m → V)
  (S Ω : Module.End ℂ V) (K : Finset ι) (c : ι → ι → ι → ℂ) (d o : Fin m → Fin m → ℂ)

theorem GlobalTheory.CompanionTheory.AnalyticWord.bnd_succ_le
    (hskew : ∀ i v w, inner ℂ (j (Z i v)) (j w) = - inner ℂ (j v) (j (Z i w)))
    (hT : ∑ i, Z i * Z i = Ω + S + S)
    (hS : ∀ i, S * Z i - Z i * S = ∑ κ ∈ K, ∑ n, c κ i n • (Z κ * Z n + Z n * Z κ))
    (hΩ : ∀ i, Ω * Z i = Z i * Ω)
    (hSy : ∀ b, S (y b) = ∑ e, d b e • y e) (hOy : ∀ b, Ω (y b) = ∑ e, o b e • y e) (n : ℕ) :
    bnd j Z y (n + 1) ≤ (√(tot o + 2 * tot d) + 2 * n * c0 K c) * bnd j Z y n := by sorry
