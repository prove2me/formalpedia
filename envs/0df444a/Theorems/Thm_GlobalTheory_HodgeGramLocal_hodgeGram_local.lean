-- Prove2me | Theorems.Thm_GlobalTheory_HodgeGramLocal_hodgeGram_local
-- name    : GlobalTheory.HodgeGramLocal.hodgeGram_local
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T23:52:14.414465+00:00
-- url     : https://prove2.me/theorems/7ea8670f-7313-4900-a5d4-d10667d17005
-- title:
--   Hodge Gram Local: hodge Gram local
-- statement:
--   The Hodge Gram Local construction uses the hodge Gram local property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HodgeMetricGramMatrixLocalHolomorphicImPart.lean#L67-L138
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HodgeMetricGramMatrixLocalHolomorphicImPart.lean#L67-L138

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_HodgePeriodGram
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_Osgood
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HodgeMetricGramMatrixLocalHolomorphicImPart
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex Filter Topology
open scoped ComplexOrder ContDiff ComplexConjugate
open GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram GlobalTheory.HermFrame
noncomputable section
open GlobalTheory GlobalTheory.HodgeGramLocal
variable {n a g : ℕ}

theorem GlobalTheory.HodgeGramLocal.hodgeGram_local (n a g rk : ℕ) (ha : a ≤ n) (τ₀ : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ)
    (B : Fin a → Matrix (Fin g) (Fin g) ℤ) (hP : IsPeriodChart rk τ₀ B) :
    ∀ z ∈ punctured ha 1, MContDiffAt ∞ (hodgeGram ha τ₀ B) z ∧
      (∀ ξ, mdel (hodgeGram ha τ₀ B) z ξ = (1 / (2 * Complex.I)) •
        ((Matrix.of fun j k => fderiv ℂ (fun x => τ₀ x j k) z ξ) +
          ∑ i, (ξ (Fin.castLE ha i) / (2 * Real.pi * Complex.I * z (Fin.castLE ha i))) •
            ((B i).map (Int.cast : ℤ → ℝ)).map Complex.ofReal)) ∧
      ∀ ξ η, mddbar (hodgeGram ha τ₀ B) z ξ η = 0 := by sorry
