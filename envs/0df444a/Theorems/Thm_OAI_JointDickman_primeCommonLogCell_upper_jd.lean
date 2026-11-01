-- Prove2me | Theorems.Thm_OAI_JointDickman_primeCommonLogCell_upper_jd
-- name    : OAI.JointDickman.primeCommonLogCell_upper_jd
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-31T20:29:12.291405+00:00
-- url     : https://prove2.me/theorems/65add99d-bef4-4a86-b01c-71dc122b893f
-- title:
--   OAI.JointDickman.primeCommonLogCell_upper_jd: intermediate lemma from OpenAI, The joint Dickman law for consecutive integers
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.JointDickmanPaper.joint_law`, `OAI.JointDickmanPaper.increasing_order` and `OAI.JointDickmanPaper.decreasing_order`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The joint Dickman law for consecutive integers*, OpenAI Math Release, September 24, 2026, result family 12, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.JointDickman.primeCommonLogCell_upper` of [lean/OAI/NumberTheory/JointDickman/Arithmetic/PrimeCommonCell.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/JointDickman/Arithmetic/PrimeCommonCell.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.JointDickman`, with `open Filter Finset`, `open scoped Topology`, `open Classical in`):
--
--   ```lean
--   theorem primeCommonLogCell_upper_jd
--       (hSD : PublishedInputs.SquarefreeSelbergDelangeInput)
--       (hSW : PublishedInputs.SquarefreeCharacterEstimateInput)
--       (hM : PublishedInputs.PrimeReciprocalMertensInput)
--       (hMP : PublishedInputs.PrimeProductMertensInput) :
--       ∃ M C : ℝ, 0 ≤ M ∧ 0 < C ∧ ∀ᶠ B : ℕ in atTop,
--         ∀ (D : Type*) [DecidableEq D], ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ (B : ℝ) ^ (100 : ℝ) →
--         ∀ lower upper : D → ℝ,
--         (∀ d e s, s ∈ Set.Ioc (lower d) (upper d) → s ∈ Set.Ioc (lower e) (upper e) → d = e) →
--         (∀ d, 1 / 2 ≤ lower d) → (∀ d, lower d ≤ upper d) → (∀ d, upper d ≤ 16 / 5) →
--         ∀ e : auxiliaryPrimes B → Bool,
--         lowPrimeLog (auxiliaryPrimes B) B (1 / 4) e → ∀ d : D, ∀ r : (ZMod q)ˣ,
--         optionCellMass (quarterPrimeMass (auxiliaryPrimes B))
--           (fun c => primeProductCell (auxiliaryPrimes B) (logResidueCell B q lower upper) c e) (d, r) ≤
--           M * (upper d - lower d) / q.totient + C * (B : ℝ) ^ (-(80 : ℝ))
--   ```
--
--   **Definitions.** The statement is written with `OAI.JointDickman.auxiliaryPrimes`, `OAI.JointDickman.logResidueCell`, `OAI.JointDickman.lowPrimeLog`, `OAI.JointDickman.optionCellMass`, `OAI.JointDickman.primeProductCell`, `OAI.JointDickman.quarterPrimeMass`, `OAI.JointDickman.PublishedInputs.PrimeProductMertensInput`, `OAI.JointDickman.PublishedInputs.PrimeReciprocalMertensInput`, `OAI.JointDickman.PublishedInputs.SquarefreeCharacterEstimateInput` and `OAI.JointDickman.PublishedInputs.SquarefreeSelbergDelangeInput` (definitions bundle `OAIQ083J001` of this split).
--
--   **Used by.** The proofs of `OAI.JointDickman.bounded_box_coarse_comparison_jd` and `OAI.JointDickman.manuscript_geometric_residue_energy_jd` of this split import it.
-- source:
--   OpenAI, The joint Dickman law for consecutive integers, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 12; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-joint-Dickman-law-for-consecutive-integers-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/JointDickman/Arithmetic/PrimeCommonCell.lean (declaration OAI.JointDickman.primeCommonLogCell_upper)

import Mathlib
import Definitions.Def_OAIQ083J001

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace JointDickman

open Filter Finset
open scoped Topology

open Classical in
theorem primeCommonLogCell_upper_jd
    (hSD : PublishedInputs.SquarefreeSelbergDelangeInput)
    (hSW : PublishedInputs.SquarefreeCharacterEstimateInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    (hMP : PublishedInputs.PrimeProductMertensInput) :
    ∃ M C : ℝ, 0 ≤ M ∧ 0 < C ∧ ∀ᶠ B : ℕ in atTop,
      ∀ (D : Type*) [DecidableEq D], ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ (B : ℝ) ^ (100 : ℝ) →
      ∀ lower upper : D → ℝ,
      (∀ d e s, s ∈ Set.Ioc (lower d) (upper d) → s ∈ Set.Ioc (lower e) (upper e) → d = e) →
      (∀ d, 1 / 2 ≤ lower d) → (∀ d, lower d ≤ upper d) → (∀ d, upper d ≤ 16 / 5) →
      ∀ e : auxiliaryPrimes B → Bool,
      lowPrimeLog (auxiliaryPrimes B) B (1 / 4) e → ∀ d : D, ∀ r : (ZMod q)ˣ,
      optionCellMass (quarterPrimeMass (auxiliaryPrimes B))
        (fun c => primeProductCell (auxiliaryPrimes B) (logResidueCell B q lower upper) c e) (d, r) ≤
        M * (upper d - lower d) / q.totient + C * (B : ℝ) ^ (-(80 : ℝ)) := by
  sorry

end JointDickman

end OAI
end
