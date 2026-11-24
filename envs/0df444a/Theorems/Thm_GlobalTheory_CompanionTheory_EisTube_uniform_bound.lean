-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_EisTube_uniform_bound
-- name    : GlobalTheory.CompanionTheory.EisTube.uniform_bound
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T11:37:04.595854+00:00
-- url     : https://prove2.me/theorems/bafe2ac1-d8c6-4547-a63f-12264ec821af
-- title:
--   Eis Tube: uniform bound
-- statement:
--   The Eis Tube construction uses the uniform bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/IntegrableExpNegSumAbs.lean#L29-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/IntegrableExpNegSumAbs.lean#L29-L53

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IntegrableExpNegSumAbs
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Topology
universe u
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.EisTube

theorem GlobalTheory.CompanionTheory.EisTube.uniform_bound {ι : Type} [Fintype ι] {P : Type u} {h : P → ℝ} (hh : ∀ p, 0 ≤ h p)
    {ψ : P → (ι → ℝ) → ℂ}
    (hψ : ∀ v : ι → ℝ, ∃ C : ℝ, ∀ p t, ‖ψ p t‖ ≤ C * h p * Real.exp (-(2 * Real.pi * ∑ i, v i * t i)))
    (R : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p t, ‖ψ p t‖ ≤ C * h p * Real.exp (-(2 * Real.pi * (R * ∑ i, |t i|))) := by sorry
