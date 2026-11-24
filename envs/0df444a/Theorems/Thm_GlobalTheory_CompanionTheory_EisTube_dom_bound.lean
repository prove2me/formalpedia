-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_EisTube_dom_bound
-- name    : GlobalTheory.CompanionTheory.EisTube.dom_bound
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T11:36:40.338073+00:00
-- url     : https://prove2.me/theorems/8f42ca8a-bb38-4819-96af-1075ac3d4fb5
-- title:
--   Eis Tube: dom bound
-- statement:
--   The Eis Tube construction uses the dom bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/IntegrableExpNegSumAbs.lean#L72-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/IntegrableExpNegSumAbs.lean#L72-L86

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

theorem GlobalTheory.CompanionTheory.EisTube.dom_bound {ι : Type} [Fintype ι] {P : Type u} {h : P → ℝ} (hh : ∀ p, 0 ≤ h p)
    {ψ : P → (ι → ℝ) → ℂ} {C B : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ p t, ‖ψ p t‖ ≤ C * h p * Real.exp (-(2 * Real.pi * ((B + 1) * ∑ i, |t i|))))
    {z : ι → ℂ} (hz : ∀ i, |(z i).re| ≤ B) (p : P) (t : ι → ℝ) :
    ‖ψ p t * ker z t‖ ≤ C * h p * Real.exp (-(2 * Real.pi * ∑ i, |t i|)) := by sorry
