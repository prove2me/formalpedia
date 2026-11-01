-- Prove2me | Theorems.Thm_OAI_JointDickman_finite_graph_centered_mean_proved_jd
-- name    : OAI.JointDickman.finite_graph_centered_mean_proved_jd
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-31T20:27:43.627289+00:00
-- url     : https://prove2.me/theorems/57e3f95a-3488-4171-8918-10b09a09f26b
-- title:
--   OAI.JointDickman.finite_graph_centered_mean_proved_jd: intermediate lemma from OpenAI, The joint Dickman law for consecutive integers
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.JointDickmanPaper.joint_law`, `OAI.JointDickmanPaper.increasing_order` and `OAI.JointDickmanPaper.decreasing_order`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The joint Dickman law for consecutive integers*, OpenAI Math Release, September 24, 2026, result family 12, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.JointDickman.finite_graph_centered_mean_proved` of [lean/OAI/NumberTheory/JointDickman/Counting/FiniteCountingMeanDischarge.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/JointDickman/Counting/FiniteCountingMeanDischarge.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.JointDickman`, with `open Finset Filter MeasureTheory Classical PublishedInputs`, `open scoped Topology`):
--
--   ```lean
--   theorem finite_graph_centered_mean_proved_jd
--       (hKMT : CharacterDistanceDivergence) (hFord : FordUpperSieveInput)
--       (hSD : SquarefreeSelbergDelangeInput) (hSW : SquarefreeCharacterEstimateInput)
--       (hM : PrimeReciprocalMertensInput) (hMP : PrimeProductMertensInput)
--       (hMC : ∀ B M : ℕ, FiniteMcDiarmidInput (Fin M) (auxiliaryPrimes B).powerset)
--       {J : ℕ} (hJ : 0 < J) (ζ : Fin (J-1) → ℂ) (hζ : ∀ i, ‖ζ i‖ = 1)
--       (μ : ℂ) (hμ : ‖μ‖ ≤ 1)
--       (hmean : ∀ D : ℝ, 0 < D → Tendsto (centeredBinPrefix J ζ μ D) atTop (𝓝 0))
--       {A L : ℕ} {cap : ℝ} (hA : 0 < A) (hL : 10000 ≤ L) (hcap : 0 < cap) :
--       ∃ τ : ℝ, 0 < τ ∧ τ ≤ cap ∧ τ ≤ samplingTau ∧
--       ∀ ε : ℝ, 0 < ε → ∃ Cmin : ℝ, 0 ≤ Cmin ∧ ∀ C : ℝ, Cmin ≤ C →
--       ∀ᶠ B : ℕ in atTop, ∀ᶠ N : ℕ in atTop,
--         let T := amplificationMultiplier B
--         let z := fun n => binLabel (fun j : Fin (J-1) => primeBin (N : ℝ) J (j.val+1)) ζ n-μ
--         (∑ u ∈ range (4*T*N), |(complexEnergy
--           (finiteGraphKernel B L T (T/A) (A*T) N u τ C) (fun i => z (u+(i.val+1)))).re|/(A*T : ℕ)) /
--             ((T : ℝ)*N) < ε
--   ```
--
--   **Definitions.** The statement is written with `OAI.JointDickman.CharacterDistanceDivergence`, `OAI.JointDickman.amplificationMultiplier`, `OAI.JointDickman.auxiliaryPrimes`, `OAI.JointDickman.binLabel`, `OAI.JointDickman.centeredBinPrefix`, `OAI.JointDickman.complexEnergy`, `OAI.JointDickman.finiteGraphKernel`, `OAI.JointDickman.primeBin`, `OAI.JointDickman.PublishedInputs.FiniteMcDiarmidInput`, `OAI.JointDickman.PublishedInputs.FordUpperSieveInput`, `OAI.JointDickman.PublishedInputs.PrimeProductMertensInput`, `OAI.JointDickman.PublishedInputs.PrimeReciprocalMertensInput`, `OAI.JointDickman.PublishedInputs.SquarefreeCharacterEstimateInput` and `OAI.JointDickman.PublishedInputs.SquarefreeSelbergDelangeInput` (definitions bundle `OAIQ083J001` of this split); `OAI.JointDickman.samplingTau` (definitions bundle `OAIQ083J002` of this split).
--
--   **Used by.** The proof of `OAI.JointDickman.rationalFixedScaleLaw_of_distance_divergence_proved_jd` of this split imports it.
-- source:
--   OpenAI, The joint Dickman law for consecutive integers, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 12; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-joint-Dickman-law-for-consecutive-integers-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/JointDickman/Counting/FiniteCountingMeanDischarge.lean (declaration OAI.JointDickman.finite_graph_centered_mean_proved)

import Mathlib
import Batteries.Tactic.Lemma
import Definitions.Def_OAIQ083J001
import Definitions.Def_OAIQ083J002

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace JointDickman
open Finset Filter MeasureTheory Classical PublishedInputs
open scoped Topology

theorem finite_graph_centered_mean_proved_jd
    (hKMT : CharacterDistanceDivergence) (hFord : FordUpperSieveInput)
    (hSD : SquarefreeSelbergDelangeInput) (hSW : SquarefreeCharacterEstimateInput)
    (hM : PrimeReciprocalMertensInput) (hMP : PrimeProductMertensInput)
    (hMC : ∀ B M : ℕ, FiniteMcDiarmidInput (Fin M) (auxiliaryPrimes B).powerset)
    {J : ℕ} (hJ : 0 < J) (ζ : Fin (J-1) → ℂ) (hζ : ∀ i, ‖ζ i‖ = 1)
    (μ : ℂ) (hμ : ‖μ‖ ≤ 1)
    (hmean : ∀ D : ℝ, 0 < D → Tendsto (centeredBinPrefix J ζ μ D) atTop (𝓝 0))
    {A L : ℕ} {cap : ℝ} (hA : 0 < A) (hL : 10000 ≤ L) (hcap : 0 < cap) :
    ∃ τ : ℝ, 0 < τ ∧ τ ≤ cap ∧ τ ≤ samplingTau ∧
    ∀ ε : ℝ, 0 < ε → ∃ Cmin : ℝ, 0 ≤ Cmin ∧ ∀ C : ℝ, Cmin ≤ C →
    ∀ᶠ B : ℕ in atTop, ∀ᶠ N : ℕ in atTop,
      let T := amplificationMultiplier B
      let z := fun n => binLabel (fun j : Fin (J-1) => primeBin (N : ℝ) J (j.val+1)) ζ n-μ
      (∑ u ∈ range (4*T*N), |(complexEnergy
        (finiteGraphKernel B L T (T/A) (A*T) N u τ C) (fun i => z (u+(i.val+1)))).re|/(A*T : ℕ)) /
          ((T : ℝ)*N) < ε := by
  sorry

end JointDickman

end OAI
end
