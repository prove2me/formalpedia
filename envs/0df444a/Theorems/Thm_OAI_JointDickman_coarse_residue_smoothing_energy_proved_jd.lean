-- Prove2me | Theorems.Thm_OAI_JointDickman_coarse_residue_smoothing_energy_proved_jd
-- name    : OAI.JointDickman.coarse_residue_smoothing_energy_proved_jd
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-31T20:24:47.063244+00:00
-- url     : https://prove2.me/theorems/c953bb7a-3fd7-40c6-9380-2b19fea9db8f
-- title:
--   OAI.JointDickman.coarse_residue_smoothing_energy_proved_jd: intermediate lemma from OpenAI, The joint Dickman law for consecutive integers
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.JointDickmanPaper.joint_law`, `OAI.JointDickmanPaper.increasing_order` and `OAI.JointDickmanPaper.decreasing_order`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The joint Dickman law for consecutive integers*, OpenAI Math Release, September 24, 2026, result family 12, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.JointDickman.coarse_residue_smoothing_energy_proved` of [lean/OAI/NumberTheory/JointDickman/Arithmetic/CoarseResidueSmoothingDischarge.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/JointDickman/Arithmetic/CoarseResidueSmoothingDischarge.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.JointDickman`, with `open Finset Filter MeasureTheory Classical PublishedInputs`, `open scoped Topology`):
--
--   ```lean
--   theorem coarse_residue_smoothing_energy_proved_jd
--       (hKMT : CharacterDistanceDivergence) (hM : PrimeReciprocalMertensInput)
--       (hSD : SquarefreeSelbergDelangeInput) (hSW : SquarefreeCharacterEstimateInput)
--       (hMP : PrimeProductMertensInput)
--       {J : ℕ} (hJ : 0 < J) (ζ : Fin (J-1) → ℂ) (hζ : ∀ i, ‖ζ i‖ = 1)
--       (μ : ℂ) (hμ : ‖μ‖ ≤ 1)
--       (hmean : ∀ D : ℝ, 0 < D → Tendsto (centeredBinPrefix J ζ μ D) atTop (𝓝 0))
--       {m : ℕ} (hm : 0 < m) (b : Fin m)
--       {q : ℕ} [NeZero q] (A scale : ℕ → ℝ) (R M : ℕ → ℕ) (hA : ∀ B, 0 < A B)
--       (hscale : Tendsto scale atTop atTop) (hR : Tendsto R atTop atTop) :
--       ∀ ε : ℝ, 0 < ε → ∀ᶠ B in atTop, ∀ᶠ n in atTop, ∀ (j : ℕ), j ≤ M B →
--         (1/(A B*scale n))*(∑ u ∈ Ico ⌈A B*scale n⌉₊ ⌊2*(A B*scale n)⌋₊,
--           ‖residueSmoothed (fun k =>
--             (binLabel (fun i : Fin (J-1) => primeBin (scale n) J (i.val+1)) ζ k-μ)*
--               (primeSiteWeight (auxiliaryPrimes B) (primeCoarseFeature m B b) k : ℂ))
--               q (R B) (u+j)‖^2) < ε
--   ```
--
--   **Definitions.** The statement is written with `OAI.JointDickman.CharacterDistanceDivergence`, `OAI.JointDickman.auxiliaryPrimes`, `OAI.JointDickman.binLabel`, `OAI.JointDickman.centeredBinPrefix`, `OAI.JointDickman.primeBin`, `OAI.JointDickman.primeCoarseFeature`, `OAI.JointDickman.primeSiteWeight`, `OAI.JointDickman.residueSmoothed`, `OAI.JointDickman.PublishedInputs.PrimeProductMertensInput`, `OAI.JointDickman.PublishedInputs.PrimeReciprocalMertensInput`, `OAI.JointDickman.PublishedInputs.SquarefreeCharacterEstimateInput` and `OAI.JointDickman.PublishedInputs.SquarefreeSelbergDelangeInput` (definitions bundle `OAIQ083J001` of this split).
--
--   **Used by.** The proof of `OAI.JointDickman.counting_model_energy_mean_proved_jd` of this split imports it.
-- source:
--   OpenAI, The joint Dickman law for consecutive integers, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 12; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-joint-Dickman-law-for-consecutive-integers-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/JointDickman/Arithmetic/CoarseResidueSmoothingDischarge.lean (declaration OAI.JointDickman.coarse_residue_smoothing_energy_proved)

import Mathlib
import Batteries.Tactic.Lemma
import Definitions.Def_OAIQ083J001

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace JointDickman
open Finset Filter MeasureTheory Classical PublishedInputs
open scoped Topology

theorem coarse_residue_smoothing_energy_proved_jd
    (hKMT : CharacterDistanceDivergence) (hM : PrimeReciprocalMertensInput)
    (hSD : SquarefreeSelbergDelangeInput) (hSW : SquarefreeCharacterEstimateInput)
    (hMP : PrimeProductMertensInput)
    {J : ℕ} (hJ : 0 < J) (ζ : Fin (J-1) → ℂ) (hζ : ∀ i, ‖ζ i‖ = 1)
    (μ : ℂ) (hμ : ‖μ‖ ≤ 1)
    (hmean : ∀ D : ℝ, 0 < D → Tendsto (centeredBinPrefix J ζ μ D) atTop (𝓝 0))
    {m : ℕ} (hm : 0 < m) (b : Fin m)
    {q : ℕ} [NeZero q] (A scale : ℕ → ℝ) (R M : ℕ → ℕ) (hA : ∀ B, 0 < A B)
    (hscale : Tendsto scale atTop atTop) (hR : Tendsto R atTop atTop) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ B in atTop, ∀ᶠ n in atTop, ∀ (j : ℕ), j ≤ M B →
      (1/(A B*scale n))*(∑ u ∈ Ico ⌈A B*scale n⌉₊ ⌊2*(A B*scale n)⌋₊,
        ‖residueSmoothed (fun k =>
          (binLabel (fun i : Fin (J-1) => primeBin (scale n) J (i.val+1)) ζ k-μ)*
            (primeSiteWeight (auxiliaryPrimes B) (primeCoarseFeature m B b) k : ℂ))
            q (R B) (u+j)‖^2) < ε := by
  sorry

end JointDickman

end OAI
end
