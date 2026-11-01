-- Prove2me | Theorems.Thm_OAI_JointDickman_counting_sampling_jd
-- name    : OAI.JointDickman.counting_sampling_jd
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-31T20:26:58.152619+00:00
-- url     : https://prove2.me/theorems/53dcc46c-ddd7-45e6-8148-fab3692c2588
-- title:
--   OAI.JointDickman.counting_sampling_jd: intermediate lemma from OpenAI, The joint Dickman law for consecutive integers
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.JointDickmanPaper.joint_law`, `OAI.JointDickmanPaper.increasing_order` and `OAI.JointDickmanPaper.decreasing_order`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The joint Dickman law for consecutive integers*, OpenAI Math Release, September 24, 2026, result family 12, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.JointDickman.counting_sampling` of [lean/OAI/NumberTheory/JointDickman/Counting/CountingSampling.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/JointDickman/Counting/CountingSampling.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.JointDickman`, with `open Finset Filter Classical PublishedInputs`, `open scoped Topology`):
--
--   ```lean
--   theorem counting_sampling_jd
--       (hFord : FordUpperSieveInput) (hSD : SquarefreeSelbergDelangeInput)
--       (hSW : SquarefreeCharacterEstimateInput) (hM : PrimeReciprocalMertensInput)
--       (hMP : PrimeProductMertensInput) {L : ℕ} {η cap : ℝ} (hL : 10000 ≤ L) (hη : 0 < η) (hcap : 0 < cap) :
--       ∃ τ : ℝ, 0 < τ ∧ τ ≤ cap ∧ τ ≤ samplingTau ∧
--         ∀ w c₁ U₁ ε : ℝ, 0 < w → 0 < c₁ → 0 ≤ U₁ → 0 < ε →
--         ∃ P : MvPolynomial (Fin 4) ℝ, ∃ c : (Fin 4 →₀ ℕ) → ℕ → ℝ,
--         (∀ d, c d 0 = squarefreeLeadingConstant (1/2) ∧ 0 < c d 0) ∧
--         ∃ D m : (Fin 4 →₀ ℕ) → ℕ, (∀ d, 0 < m d) ∧
--         ∃ Cmin : ℝ, 0 ≤ Cmin ∧
--         ∀ᶠ B : ℕ in atTop, ∀ (C : ℝ) (H M U V Q : ℕ),
--           Cmin ≤ C →
--           (∏ p ∈ auxiliaryPrimes B,p) ≤ U → ⌊Real.exp (2*(B : ℝ))⌋₊ ≤ V →
--           (∀ k ∈ dyadicBoxIndices (dyadicBoxLower B (amplificationMultiplier B))
--               (dyadicBoxUpper B (amplificationMultiplier B)),
--             ⌊(17/4 : ℝ)*Real.exp ((k : ℝ)*Real.log 2)⌋₊ ≤ U) →
--           (∀ k ∈ dyadicBoxIndices (dyadicBoxLower B (amplificationMultiplier B))
--               (dyadicBoxUpper B (amplificationMultiplier B)),
--             ⌊(17/4 : ℝ)*(Real.exp ((k : ℝ)*Real.log 2)/amplificationMultiplier B)⌋₊ ≤ V) →
--           0 < Q → (B : ℝ)^(2/5 : ℝ) ≤ Q → amplificationMultiplier B*Q ≤ B →
--           η*amplificationMultiplier B ≤ H → amplificationMultiplier B ≤ M →
--           c₁*(B : ℝ)^(0.32 : ℝ) ≤ M → (M : ℝ) ≤ U₁*(B : ℝ)^(0.32 : ℝ) →
--           FiniteMcDiarmidInput (Fin M) (auxiliaryPrimes B).powerset →
--           ∀ σ : ℝ, |σ| ≤ 3 →
--           finiteExpectation (siteProductMass (fun _ : Fin M => independentPrimeSetMass B))
--             (fun x => kernelCutNorm (realizedSiteKernel
--               (countingSiteError P m B L (amplificationMultiplier B) H M τ C w c D σ) x)) ≤ ε
--   ```
--
--   **Definitions.** The statement is written with `OAI.JointDickman.amplificationMultiplier`, `OAI.JointDickman.auxiliaryPrimes`, `OAI.JointDickman.countingSiteError`, `OAI.JointDickman.dyadicBoxIndices`, `OAI.JointDickman.dyadicBoxLower`, `OAI.JointDickman.dyadicBoxUpper`, `OAI.JointDickman.finiteExpectation`, `OAI.JointDickman.independentPrimeSetMass`, `OAI.JointDickman.kernelCutNorm`, `OAI.JointDickman.realizedSiteKernel`, `OAI.JointDickman.squarefreeLeadingConstant`, `OAI.JointDickman.PublishedInputs.FiniteMcDiarmidInput`, `OAI.JointDickman.PublishedInputs.FordUpperSieveInput`, `OAI.JointDickman.PublishedInputs.PrimeProductMertensInput`, `OAI.JointDickman.PublishedInputs.PrimeReciprocalMertensInput`, `OAI.JointDickman.PublishedInputs.SquarefreeCharacterEstimateInput`, `OAI.JointDickman.PublishedInputs.SquarefreeSelbergDelangeInput` and `OAI.JointDickman.PublishedInputs.siteProductMass` (definitions bundle `OAIQ083J001` of this split); `OAI.JointDickman.samplingTau` (definitions bundle `OAIQ083J002` of this split).
--
--   **Used by.** The proof of `OAI.JointDickman.counting_sampling_actual_scale_jd` of this split imports it.
-- source:
--   OpenAI, The joint Dickman law for consecutive integers, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 12; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-joint-Dickman-law-for-consecutive-integers-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/JointDickman/Counting/CountingSampling.lean (declaration OAI.JointDickman.counting_sampling)

import Mathlib
import Definitions.Def_OAIQ083J001
import Definitions.Def_OAIQ083J002

section

attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace JointDickman
open Finset Filter Classical PublishedInputs
open scoped Topology

theorem counting_sampling_jd
    (hFord : FordUpperSieveInput) (hSD : SquarefreeSelbergDelangeInput)
    (hSW : SquarefreeCharacterEstimateInput) (hM : PrimeReciprocalMertensInput)
    (hMP : PrimeProductMertensInput) {L : ℕ} {η cap : ℝ} (hL : 10000 ≤ L) (hη : 0 < η) (hcap : 0 < cap) :
    ∃ τ : ℝ, 0 < τ ∧ τ ≤ cap ∧ τ ≤ samplingTau ∧
      ∀ w c₁ U₁ ε : ℝ, 0 < w → 0 < c₁ → 0 ≤ U₁ → 0 < ε →
      ∃ P : MvPolynomial (Fin 4) ℝ, ∃ c : (Fin 4 →₀ ℕ) → ℕ → ℝ,
      (∀ d, c d 0 = squarefreeLeadingConstant (1/2) ∧ 0 < c d 0) ∧
      ∃ D m : (Fin 4 →₀ ℕ) → ℕ, (∀ d, 0 < m d) ∧
      ∃ Cmin : ℝ, 0 ≤ Cmin ∧
      ∀ᶠ B : ℕ in atTop, ∀ (C : ℝ) (H M U V Q : ℕ),
        Cmin ≤ C →
        (∏ p ∈ auxiliaryPrimes B,p) ≤ U → ⌊Real.exp (2*(B : ℝ))⌋₊ ≤ V →
        (∀ k ∈ dyadicBoxIndices (dyadicBoxLower B (amplificationMultiplier B))
            (dyadicBoxUpper B (amplificationMultiplier B)),
          ⌊(17/4 : ℝ)*Real.exp ((k : ℝ)*Real.log 2)⌋₊ ≤ U) →
        (∀ k ∈ dyadicBoxIndices (dyadicBoxLower B (amplificationMultiplier B))
            (dyadicBoxUpper B (amplificationMultiplier B)),
          ⌊(17/4 : ℝ)*(Real.exp ((k : ℝ)*Real.log 2)/amplificationMultiplier B)⌋₊ ≤ V) →
        0 < Q → (B : ℝ)^(2/5 : ℝ) ≤ Q → amplificationMultiplier B*Q ≤ B →
        η*amplificationMultiplier B ≤ H → amplificationMultiplier B ≤ M →
        c₁*(B : ℝ)^(0.32 : ℝ) ≤ M → (M : ℝ) ≤ U₁*(B : ℝ)^(0.32 : ℝ) →
        FiniteMcDiarmidInput (Fin M) (auxiliaryPrimes B).powerset →
        ∀ σ : ℝ, |σ| ≤ 3 →
        finiteExpectation (siteProductMass (fun _ : Fin M => independentPrimeSetMass B))
          (fun x => kernelCutNorm (realizedSiteKernel
            (countingSiteError P m B L (amplificationMultiplier B) H M τ C w c D σ) x)) ≤ ε := by
  sorry

end JointDickman

end OAI
end
