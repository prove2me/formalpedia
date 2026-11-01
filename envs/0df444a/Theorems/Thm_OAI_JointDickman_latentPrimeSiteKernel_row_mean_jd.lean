-- Prove2me | Theorems.Thm_OAI_JointDickman_latentPrimeSiteKernel_row_mean_jd
-- name    : OAI.JointDickman.latentPrimeSiteKernel_row_mean_jd
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-31T20:33:45.576303+00:00
-- url     : https://prove2.me/theorems/47754318-6c4c-4f20-ac47-632666da870b
-- title:
--   OAI.JointDickman.latentPrimeSiteKernel_row_mean_jd: intermediate lemma from OpenAI, The joint Dickman law for consecutive integers
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.JointDickmanPaper.joint_law`, `OAI.JointDickmanPaper.increasing_order` and `OAI.JointDickmanPaper.decreasing_order`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The joint Dickman law for consecutive integers*, OpenAI Math Release, September 24, 2026, result family 12, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.JointDickman.latentPrimeSiteKernel_row_mean` of [lean/OAI/NumberTheory/JointDickman/Amplification/CandidateExpectedDegree.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/JointDickman/Amplification/CandidateExpectedDegree.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.JointDickman`, with `open Finset Filter Classical`, `open scoped Topology`):
--
--   ```lean
--   theorem latentPrimeSiteKernel_row_mean_jd
--       (hFord : PublishedInputs.FordUpperSieveInput)
--       (hM : PublishedInputs.PrimeReciprocalMertensInput) :
--       ∃ K : ℝ, 0 < K ∧ ∀ᶠ B : ℕ in atTop, ∀ (L T H M : ℕ) (τ C : ℝ),
--         0 < T → (T : ℝ) ≤ Real.exp ((1/10 : ℝ)*B) →
--         ∀ χ : BlockCandidateIndex M → ℝ, (∀ e, 0 ≤ χ e ∧ χ e ≤ 1) →
--         ∀ (i : Fin M) (a : (auxiliaryPrimes B).powerset),
--         |siteRowMean (fun _ : Fin M => independentPrimeSetMass B)
--           (latentPrimeSiteKernel B L T H M τ C χ) i a| ≤ K
--   ```
--
--   **Definitions.** The statement is written with `OAI.JointDickman.BlockCandidateIndex`, `OAI.JointDickman.auxiliaryPrimes`, `OAI.JointDickman.independentPrimeSetMass`, `OAI.JointDickman.latentPrimeSiteKernel`, `OAI.JointDickman.PublishedInputs.FordUpperSieveInput` and `OAI.JointDickman.PublishedInputs.PrimeReciprocalMertensInput` (definitions bundle `OAIQ083J001` of this split); `OAI.JointDickman.siteRowMean` (definitions bundle `OAIQ083J003` of this split).
--
--   **Used by.** The proof of `OAI.JointDickman.counting_sampling_jd` of this split imports it.
-- source:
--   OpenAI, The joint Dickman law for consecutive integers, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 12; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-joint-Dickman-law-for-consecutive-integers-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/JointDickman/Amplification/CandidateExpectedDegree.lean (declaration OAI.JointDickman.latentPrimeSiteKernel_row_mean)

import Mathlib
import Definitions.Def_OAIQ083J003

section

attribute [-instance] _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.TwoPointCorrelations.modulusProduct_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace JointDickman
open Finset Filter Classical
open scoped Topology

theorem latentPrimeSiteKernel_row_mean_jd
    (hFord : PublishedInputs.FordUpperSieveInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ B : ℕ in atTop, ∀ (L T H M : ℕ) (τ C : ℝ),
      0 < T → (T : ℝ) ≤ Real.exp ((1/10 : ℝ)*B) →
      ∀ χ : BlockCandidateIndex M → ℝ, (∀ e, 0 ≤ χ e ∧ χ e ≤ 1) →
      ∀ (i : Fin M) (a : (auxiliaryPrimes B).powerset),
      |siteRowMean (fun _ : Fin M => independentPrimeSetMass B)
        (latentPrimeSiteKernel B L T H M τ C χ) i a| ≤ K := by
  sorry

end JointDickman

end OAI
end
