-- Prove2me | Theorems.Thm_OAI_JointDickman_primeChannelMarginal_upper_jd
-- name    : OAI.JointDickman.primeChannelMarginal_upper_jd
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-31T20:28:53.206502+00:00
-- url     : https://prove2.me/theorems/9ad2929e-936d-4145-9138-9239b7ff5915
-- title:
--   OAI.JointDickman.primeChannelMarginal_upper_jd: intermediate lemma from OpenAI, The joint Dickman law for consecutive integers
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.JointDickmanPaper.joint_law`, `OAI.JointDickmanPaper.increasing_order` and `OAI.JointDickmanPaper.decreasing_order`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The joint Dickman law for consecutive integers*, OpenAI Math Release, September 24, 2026, result family 12, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.JointDickman.primeChannelMarginal_upper` of [lean/OAI/NumberTheory/JointDickman/Arithmetic/PrimeChannelMarginal.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/JointDickman/Arithmetic/PrimeChannelMarginal.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.JointDickman`, with `open Filter Finset`, `open scoped Topology`, `open Classical in`):
--
--   ```lean
--   theorem primeChannelMarginal_upper_jd
--       (hSD : PublishedInputs.SquarefreeSelbergDelangeInput)
--       (hSW : PublishedInputs.SquarefreeCharacterEstimateInput)
--       (hM : PublishedInputs.PrimeReciprocalMertensInput)
--       (hMP : PublishedInputs.PrimeProductMertensInput) :
--       ∃ M C : ℝ, 0 ≤ M ∧ 0 < C ∧ ∀ᶠ B : ℕ in atTop,
--         ∀ (D : Type*) [DecidableEq D], ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ (B : ℝ) ^ (100 : ℝ) →
--         ∀ lower upper : D → ℝ,
--         (∀ d e s, s ∈ Set.Ioc (lower d) (upper d) → s ∈ Set.Ioc (lower e) (upper e) → d = e) →
--         (∀ d, 1 / 4 ≤ lower d) → (∀ d, lower d ≤ upper d) → (∀ d, upper d ≤ 16 / 5) →
--         ∀ d : D, ∀ r : (ZMod q)ˣ,
--         independentCellMarginal (quarterPrimeMass (auxiliaryPrimes B))
--           (quarterPrimeMass (auxiliaryPrimes B))
--           (primeProductCell (auxiliaryPrimes B) (logResidueCell B q lower upper)) (d, r) ≤
--           M * (upper d - lower d) / q.totient + C * (B : ℝ) ^ (-(80 : ℝ)) +
--             9 / (8 * (auxiliaryCutoff B : ℝ))
--   ```
--
--   **Definitions.** The statement is written with `OAI.JointDickman.auxiliaryCutoff`, `OAI.JointDickman.auxiliaryPrimes`, `OAI.JointDickman.independentCellMarginal`, `OAI.JointDickman.logResidueCell`, `OAI.JointDickman.primeProductCell`, `OAI.JointDickman.quarterPrimeMass`, `OAI.JointDickman.PublishedInputs.PrimeProductMertensInput`, `OAI.JointDickman.PublishedInputs.PrimeReciprocalMertensInput`, `OAI.JointDickman.PublishedInputs.SquarefreeCharacterEstimateInput` and `OAI.JointDickman.PublishedInputs.SquarefreeSelbergDelangeInput` (definitions bundle `OAIQ083J001` of this split).
--
--   **Used by.** The proofs of `OAI.JointDickman.bounded_box_coarse_comparison_jd` and `OAI.JointDickman.manuscript_geometric_residue_energy_jd` of this split import it.
-- source:
--   OpenAI, The joint Dickman law for consecutive integers, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 12; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-joint-Dickman-law-for-consecutive-integers-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/JointDickman/Arithmetic/PrimeChannelMarginal.lean (declaration OAI.JointDickman.primeChannelMarginal_upper)

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
theorem primeChannelMarginal_upper_jd
    (hSD : PublishedInputs.SquarefreeSelbergDelangeInput)
    (hSW : PublishedInputs.SquarefreeCharacterEstimateInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    (hMP : PublishedInputs.PrimeProductMertensInput) :
    ∃ M C : ℝ, 0 ≤ M ∧ 0 < C ∧ ∀ᶠ B : ℕ in atTop,
      ∀ (D : Type*) [DecidableEq D], ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ (B : ℝ) ^ (100 : ℝ) →
      ∀ lower upper : D → ℝ,
      (∀ d e s, s ∈ Set.Ioc (lower d) (upper d) → s ∈ Set.Ioc (lower e) (upper e) → d = e) →
      (∀ d, 1 / 4 ≤ lower d) → (∀ d, lower d ≤ upper d) → (∀ d, upper d ≤ 16 / 5) →
      ∀ d : D, ∀ r : (ZMod q)ˣ,
      independentCellMarginal (quarterPrimeMass (auxiliaryPrimes B))
        (quarterPrimeMass (auxiliaryPrimes B))
        (primeProductCell (auxiliaryPrimes B) (logResidueCell B q lower upper)) (d, r) ≤
        M * (upper d - lower d) / q.totient + C * (B : ℝ) ^ (-(80 : ℝ)) +
          9 / (8 * (auxiliaryCutoff B : ℝ)) := by
  sorry

end JointDickman

end OAI
end
