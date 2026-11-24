-- Prove2me | Theorems.Thm_GlobalTheory_Lin_PsiToPi_step
-- name    : GlobalTheory.Lin.PsiToPi.step
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T18:05:53.984669+00:00
-- url     : https://prove2.me/theorems/4ffec614-03b4-48f7-a090-fb4dba32f987
-- title:
--   Psi To Pi: step
-- statement:
--   The Psi To Pi construction uses the step property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/PrimeCountRelativeErrorOfPsiRelativeError.lean#L215-L301
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/PrimeCountRelativeErrorOfPsiRelativeError.lean#L215-L301

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_ZerosDisc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_PrimeCountRelativeErrorOfPsiRelativeError
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology GlobalTheory.Lin
open scoped Classical
open GlobalTheory GlobalTheory.Lin GlobalTheory.Lin.PsiToPi
open Formalism.HermitianLattices.GL2PrimeSums (Li Emain)

theorem GlobalTheory.Lin.PsiToPi.step (P : ℕ → Prop) {θ : ℤ} {β δ φ B ρ s : ℝ} (hθ : θ = 0 ∨ θ = 1 ∨ θ = -1) (hβ : 7 / 8 ≤ β) (hδ : 0 < δ)
    (hδβ : δ ≤ 1 - β) (hB : 3 ≤ B) (hφ : 0 ≤ φ) (hφB : φ ≤ B) (hρ : 0 ≤ ρ) (hs : 64 * B ≤ δ * s)
    (h : ∀ u ∈ Set.Icc (s ^ 8) (s ^ 16),
      |φ * (∑ n ∈ (Finset.Icc 1 ⌊u⌋₊).filter P, Λ n) - mainPsi θ β u| ≤ ρ * mainPsi θ β u) :
    0 ≤ Emain θ β (s ^ 16) ∧
      |φ * cnt P (s ^ 16) - Emain θ β (s ^ 16)| ≤ (3 * ρ + 4 / s) * Emain θ β (s ^ 16) := by sorry
