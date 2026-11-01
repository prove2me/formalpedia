-- Prove2me | Theorems.Thm_OAI_JointDickman_manuscript_geometric_residue_energy_jd
-- name    : OAI.JointDickman.manuscript_geometric_residue_energy_jd
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-31T20:28:15.735198+00:00
-- url     : https://prove2.me/theorems/e43e3c99-6e77-4ed4-a447-e1072d40c391
-- title:
--   OAI.JointDickman.manuscript_geometric_residue_energy_jd: intermediate lemma from OpenAI, The joint Dickman law for consecutive integers
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.JointDickmanPaper.joint_law`, `OAI.JointDickmanPaper.increasing_order` and `OAI.JointDickmanPaper.decreasing_order`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The joint Dickman law for consecutive integers*, OpenAI Math Release, September 24, 2026, result family 12, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.JointDickman.manuscript_geometric_residue_energy` of [lean/OAI/NumberTheory/JointDickman/Counting/ResidueBoxEnergy.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/JointDickman/Counting/ResidueBoxEnergy.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.JointDickman`, with `open Finset Filter`, `open scoped Topology`):
--
--   ```lean
--   theorem manuscript_geometric_residue_energy_jd
--       (hSD : PublishedInputs.SquarefreeSelbergDelangeInput)
--       (hSW : PublishedInputs.SquarefreeCharacterEstimateInput)
--       (hM : PublishedInputs.PrimeReciprocalMertensInput)
--       (hMP : PublishedInputs.PrimeProductMertensInput) :
--       ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, 0 < m → ∀ᶠ B : ℕ in atTop,
--         ∀ q : ℕ, [NeZero q] → q ≤ B →
--         ∀ t L U : ℝ, 0 < t → L ≤ U → ∀ S : Finset ℤ,
--         ∀ g : (auxiliaryPrimes B → Bool) → ℝ,
--         (∑ k ∈ S, manuscriptResidueEnergy m B q
--           (histogramWindowCells (channelFineCount m B) (((k : ℝ)*t+L)/B) (((k : ℝ)*t+U)/B)) g) ≤
--           ((q : ℝ)/(q.totient : ℝ))*((U-L+2)/B)*C*((1+U-L)/t+1)*
--             (B : ℝ)^(-(1/40 : ℝ))*(∑ x, fullPrimeMass (auxiliaryPrimes B) x*g x^2)
--   ```
--
--   **Definitions.** The statement is written with `OAI.JointDickman.auxiliaryPrimes`, `OAI.JointDickman.channelFineCount`, `OAI.JointDickman.fullPrimeMass`, `OAI.JointDickman.histogramWindowCells`, `OAI.JointDickman.manuscriptResidueEnergy`, `OAI.JointDickman.PublishedInputs.PrimeProductMertensInput`, `OAI.JointDickman.PublishedInputs.PrimeReciprocalMertensInput`, `OAI.JointDickman.PublishedInputs.SquarefreeCharacterEstimateInput` and `OAI.JointDickman.PublishedInputs.SquarefreeSelbergDelangeInput` (definitions bundle `OAIQ083J001` of this split).
--
--   **Used by.** The proof of `OAI.JointDickman.geometric_sampled_integral_error_sum_jd` of this split imports it.
-- source:
--   OpenAI, The joint Dickman law for consecutive integers, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 12; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-joint-Dickman-law-for-consecutive-integers-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/JointDickman/Counting/ResidueBoxEnergy.lean (declaration OAI.JointDickman.manuscript_geometric_residue_energy)

import Mathlib
import Definitions.Def_OAIQ083J001

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace JointDickman
open Finset Filter
open scoped Topology

theorem manuscript_geometric_residue_energy_jd
    (hSD : PublishedInputs.SquarefreeSelbergDelangeInput)
    (hSW : PublishedInputs.SquarefreeCharacterEstimateInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    (hMP : PublishedInputs.PrimeProductMertensInput) :
    ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, 0 < m → ∀ᶠ B : ℕ in atTop,
      ∀ q : ℕ, [NeZero q] → q ≤ B →
      ∀ t L U : ℝ, 0 < t → L ≤ U → ∀ S : Finset ℤ,
      ∀ g : (auxiliaryPrimes B → Bool) → ℝ,
      (∑ k ∈ S, manuscriptResidueEnergy m B q
        (histogramWindowCells (channelFineCount m B) (((k : ℝ)*t+L)/B) (((k : ℝ)*t+U)/B)) g) ≤
        ((q : ℝ)/(q.totient : ℝ))*((U-L+2)/B)*C*((1+U-L)/t+1)*
          (B : ℝ)^(-(1/40 : ℝ))*(∑ x, fullPrimeMass (auxiliaryPrimes B) x*g x^2) := by
  sorry

end JointDickman

end OAI
end
