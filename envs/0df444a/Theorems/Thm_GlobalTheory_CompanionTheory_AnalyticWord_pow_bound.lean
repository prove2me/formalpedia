-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_AnalyticWord_pow_bound
-- name    : GlobalTheory.CompanionTheory.AnalyticWord.pow_bound
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T11:18:13.6404+00:00
-- url     : https://prove2.me/theorems/af81036d-7b6a-4ed1-9750-66d23b814706
-- title:
--   Analytic Word: pow bound
-- statement:
--   The Analytic Word construction uses the pow bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/SkewAdjointCasimirSpectral.lean#L315-L340
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/SkewAdjointCasimirSpectral.lean#L315-L340

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

theorem GlobalTheory.CompanionTheory.AnalyticWord.pow_bound (x : ι → ℂ) (k : ℕ) : ∀ (p : List ι) (e : Fin m),
    ‖j (word Z p (((∑ i, x i • Z i) ^ k) (y e)))‖ ≤
      (∑ i, ‖x i‖) ^ k * bnd j Z y (p.length + k) := by sorry
