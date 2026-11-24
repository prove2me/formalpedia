-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_AnalyticWord_comm_term
-- name    : GlobalTheory.CompanionTheory.AnalyticWord.comm_term
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T11:17:51.34127+00:00
-- url     : https://prove2.me/theorems/d43f351b-6050-4e71-8bd1-736c1bad7dc9
-- title:
--   Analytic Word: comm term
-- statement:
--   The Analytic Word construction uses the comm term property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/SkewAdjointCasimirSpectral.lean#L129-L161
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/SkewAdjointCasimirSpectral.lean#L129-L161

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

theorem GlobalTheory.CompanionTheory.AnalyticWord.comm_term
    (hS : ∀ i, S * Z i - Z i * S = ∑ κ ∈ K, ∑ n, c κ i n • (Z κ * Z n + Z n * Z κ))
    (p l : List ι) (i : ι) (e : Fin m) :
    ‖j (word Z p ((S * Z i - Z i * S) (word Z l (y e))))‖ ≤
      c0 K c * bnd j Z y (p.length + l.length + 2) := by sorry
