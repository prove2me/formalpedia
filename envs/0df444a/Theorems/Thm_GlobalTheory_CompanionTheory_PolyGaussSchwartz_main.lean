-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_PolyGaussSchwartz_main
-- name    : GlobalTheory.CompanionTheory.PolyGaussSchwartz.main
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T12:01:34.440838+00:00
-- url     : https://prove2.me/theorems/bedaea8a-3e8e-5d1c-921a-48a0528d8c46
-- title:
--   Poly Gauss Schwartz: main
-- statement:
--   The Poly Gauss Schwartz construction uses the main property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsSchwartzPolyMulGauss.lean#L78-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsSchwartzPolyMulGauss.lean#L78-L81

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_GaussianSchwartz
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsSchwartzPolyMulGauss
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.PolyGaussSchwartz
variable {m n : ℕ}

theorem GlobalTheory.CompanionTheory.PolyGaussSchwartz.main : ∀ (m n : ℕ) (P : MvPolynomial (Fin m × Fin n × Bool) ℂ), ∃ φ : SchwartzMap (Fin m → Fin n → ℂ) ℂ,
    ⇑φ = fun u => MvPolynomial.eval (fun k => if k.2.2 then star (u k.1 k.2.1) else u k.1 k.2.1) P *
      Complex.exp (-(2 * Real.pi * ∑ a, ∑ i, ‖u a i‖ ^ 2 : ℝ)) := by sorry
