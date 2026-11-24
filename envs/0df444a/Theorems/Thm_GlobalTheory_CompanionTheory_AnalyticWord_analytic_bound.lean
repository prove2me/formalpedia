-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_AnalyticWord_analytic_bound
-- name    : GlobalTheory.CompanionTheory.AnalyticWord.analytic_bound
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T13:53:51.900802+00:00
-- url     : https://prove2.me/theorems/d02cea13-fdc1-46df-b139-8806673a31d1
-- title:
--   Analytic Word: analytic bound
-- statement:
--   The Analytic Word construction uses the analytic bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/SkewAdjointCasimirSpectral.lean#L344-L383
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/SkewAdjointCasimirSpectral.lean#L344-L383

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

theorem GlobalTheory.CompanionTheory.AnalyticWord.analytic_bound : ∀ (V H : Type) [AddCommGroup V] [Module ℂ V] [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (j : V →ₗ[ℂ] H) (ι : Type) [Fintype ι] [DecidableEq ι]
    (Z : ι → Module.End ℂ V) (K : Finset ι) (m : ℕ) (y : Fin m → V) (d o : Fin m → Fin m → ℂ)
    (c : ι → ι → ι → ℂ),
    (∀ i v w, inner ℂ (j (Z i v)) (j w) = - inner ℂ (j v) (j (Z i w))) →
    (∀ κ i, Z κ * Z i - Z i * Z κ = ∑ l, c κ i l • Z l) →
    (∀ i, (∑ i ∈ Kᶜ, Z i * Z i - ∑ κ ∈ K, Z κ * Z κ) * Z i =
      Z i * (∑ i ∈ Kᶜ, Z i * Z i - ∑ κ ∈ K, Z κ * Z κ)) →
    (∀ b, (∑ κ ∈ K, Z κ * Z κ) (y b) = ∑ e, d b e • y e) →
    (∀ b, (∑ i ∈ Kᶜ, Z i * Z i - ∑ κ ∈ K, Z κ * Z κ) (y b) = ∑ e, o b e • y e) →
    ∀ (x : ι → ℂ), ∀ v ∈ Submodule.span ℂ (Set.range y), ∃ M C : ℝ, ∀ k : ℕ,
      ‖j (((∑ i, x i • Z i) ^ k) v)‖ ≤ M * C ^ k * (k.factorial : ℝ) := by sorry
