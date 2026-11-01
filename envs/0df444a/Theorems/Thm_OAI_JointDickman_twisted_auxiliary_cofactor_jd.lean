-- Prove2me | Theorems.Thm_OAI_JointDickman_twisted_auxiliary_cofactor_jd
-- name    : OAI.JointDickman.twisted_auxiliary_cofactor_jd
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-31T20:35:22.633199+00:00
-- url     : https://prove2.me/theorems/1a7bae1e-6fad-45c1-bb7a-8df6cb2fef2f
-- title:
--   OAI.JointDickman.twisted_auxiliary_cofactor_jd: intermediate lemma from OpenAI, The joint Dickman law for consecutive integers
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.JointDickmanPaper.joint_law`, `OAI.JointDickmanPaper.increasing_order` and `OAI.JointDickmanPaper.decreasing_order`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The joint Dickman law for consecutive integers*, OpenAI Math Release, September 24, 2026, result family 12, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.JointDickman.twisted_auxiliary_cofactor` of [lean/OAI/NumberTheory/JointDickman/Amplification/TwistedAuxiliaryCofactor.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/JointDickman/Amplification/TwistedAuxiliaryCofactor.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.JointDickman`, with `open Finset Filter TwoPointCorrelations`, `open scoped Classical Topology`):
--
--   ```lean
--   theorem twisted_auxiliary_cofactor_jd {ι : Type*} [Fintype ι]
--       {J : ℕ} (hJ : 0 < J) (j : ι → ℕ) (hj : ∀ i, 1 ≤ j i)
--       (E : Finset ℕ) (hE : ∀ p ∈ E, p.Prime) {A H α β : ℝ}
--       (hA : 0 < A) (hH : 2 ≤ H) (hα : 0 < α) (hαβ : α ≤ β)
--       (hαJ : α ≤ (1:ℝ)/J) (hβ : β < 1/12)
--       {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
--       {ε : ℝ} (hε : 0 < ε) :
--       ∀ᶠ N : ℕ in atTop, ∀ x : ℝ, (N:ℝ)/A ≤ x →
--         ∀ (m : ℕ) (a : ι → Fin m) (w : ℕ → ℝ),
--         (∀ p ∈ E, 0 ≤ w p ∧ w p ≤ 1) →
--         ∀ k ∈ auxiliaryLogBins H α β N, ∀ t : ℝ, |t| ≤ N →
--         ‖mrtCofactorPolynomial (mrtPrimeBand ((N:ℝ)^α) ((N:ℝ)^β))
--           (twistedWeightedBinInterpolant (fun i => primeBin x J (j i))
--             (finitePrimeWeight E w) a χ) N (mrtPrimeLogLower H k) t‖ ≤ ε
--   ```
--
--   **Definitions.** The statement is written with `OAI.JointDickman.auxiliaryLogBins`, `OAI.JointDickman.finitePrimeWeight`, `OAI.JointDickman.primeBin`, `OAI.TwoPointCorrelations.mrtPrimeBand` and `OAI.TwoPointCorrelations.mrtPrimeLogLower` (definitions bundle `OAIQ083J001` of this split); `OAI.TwoPointCorrelations.mrtCofactorPolynomial` (definitions bundle `OAIQ083J002` of this split); `OAI.JointDickman.twistedWeightedBinInterpolant` (definitions bundle `OAIQ083J003` of this split).
--
--   **Used by.** The proof of `OAI.JointDickman.twisted_bin_spectral_jd` of this split imports it.
-- source:
--   OpenAI, The joint Dickman law for consecutive integers, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 12; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-joint-Dickman-law-for-consecutive-integers-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/JointDickman/Amplification/TwistedAuxiliaryCofactor.lean (declaration OAI.JointDickman.twisted_auxiliary_cofactor)

import Mathlib
import Batteries.Tactic.Lemma
import Definitions.Def_OAIQ083J003

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace JointDickman
open Finset Filter TwoPointCorrelations
open scoped Classical Topology

theorem twisted_auxiliary_cofactor_jd {ι : Type*} [Fintype ι]
    {J : ℕ} (hJ : 0 < J) (j : ι → ℕ) (hj : ∀ i, 1 ≤ j i)
    (E : Finset ℕ) (hE : ∀ p ∈ E, p.Prime) {A H α β : ℝ}
    (hA : 0 < A) (hH : 2 ≤ H) (hα : 0 < α) (hαβ : α ≤ β)
    (hαJ : α ≤ (1:ℝ)/J) (hβ : β < 1/12)
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ x : ℝ, (N:ℝ)/A ≤ x →
      ∀ (m : ℕ) (a : ι → Fin m) (w : ℕ → ℝ),
      (∀ p ∈ E, 0 ≤ w p ∧ w p ≤ 1) →
      ∀ k ∈ auxiliaryLogBins H α β N, ∀ t : ℝ, |t| ≤ N →
      ‖mrtCofactorPolynomial (mrtPrimeBand ((N:ℝ)^α) ((N:ℝ)^β))
        (twistedWeightedBinInterpolant (fun i => primeBin x J (j i))
          (finitePrimeWeight E w) a χ) N (mrtPrimeLogLower H k) t‖ ≤ ε := by
  sorry

end JointDickman

end OAI
end
